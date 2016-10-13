import macros
import debug,utils,seqset,tensorTypes,indexTypes
proc treerepr(t: dummyTree): string {.compileTime.} =
  proc `$`(s: seqset[NimNode]): string =
    result = "["
    for i in s:
      result &= i.repr & ","
    if ',' == result[^1]: result[^1] = ']'
    else: result &= "]"
  proc go(t: dummyTree, pre: string): string =
    result = pre & $t.idx & "\n"
    if t.branch.len > 0:
      for i in t.branch:
        result &= go(i, pre & "  ")
  return go(t, "")
proc newTensorAssign(lhs, rhs: NimNode): NimNode =
  # Use `+=`, assuming new tensors are initialized with 0.
  if lhs.len == 1:
    #result = infix(lhs[0], "+=", rhs)
    result = newAssignment(lhs[0], rhs)
    #result = newAssignment(lhs[0], infix(lhs[0],"+",rhs))
  elif lhs.len > 1:
    #result = infix(lhs, "+=", rhs)
    result = newAssignment(lhs, rhs)
    #result = newAssignment(lhs, infix(lhs,"+",rhs))
  else:
    error "Don't know how to assign rhs: " & rhs.treerepr & " to lhs: " & lhs.treerepr
macro defTensorEq(lhs: untyped, rhs: typed): untyped =
  # TODO: We can keep the definition as a function so we can optimize away,
  # or remove the unused indices later.
  dbg "defTensorEq:lhs: ", lhs, TPLDebug.detail
  dbg "defTensorEq:rhs: ", rhs, TPLDebug.detail
  result = newStmtList().add(newNimNode(nnkVarSection), newTensorAssign(lhs, rhs))
  let rhsT = newCall(bindsym"type", rhs)
  if lhs.kind == nnkBracketExpr:
    if lhs.len > 1:
      var tensorCall = newCall(bindsym"Tensor", newNimNode(nnkBracket), rhsT)
      for i in 1..<lhs.len:
        tensorCall[1].add newCall(bindsym"type", lhs[i])
      result[0].add newIdentDefs(lhs[0], tensorCall)
    elif lhs.len == 1:
      result[0].add newIdentDefs(lhs[0], rhsT)
    else:
      error "Don't know how to create temporaryTensor from lhs: '" & lhs.repr & "' and rhs: '" & rhs.repr & "'"
  elif lhs.kind == nnkIdent or lhs.kind == nnkSym:
    result[0].add newIdentDefs(lhs, rhsT)
  else:
    error "Don't know how to create temporaryTensor from lhs: '" & lhs.repr & "' and rhs: '" & rhs.repr & "'"
  dbg "defTensorEq:result => ", result, TPLDebug.detail
proc needAutoSum(n: NimNode, t: dummyTree): bool =
  let rhsLocalIx = t.idx - t.branch.getlhsix
  result = n.isAutoSumStmt and rhsLocalIx.len > 0
const temporaryTensorPrefix = "__Ttmp:"
var temporaryTensorId {.compileTime.} = 0
proc temporaryTensor(ix: seqset[NimNode], rhs: NimNode): (NimNode, NimNode) =
  # Returns a tensor of BracketExpr[T,ix...] or a scalar of
  # nnkSym, and the definition.
  var tt = newNimNode(nnkBracketExpr).add gensym(nskVar, temporaryTensorPrefix & $temporaryTensorId)
  inc temporaryTensorId
  if ix.len > 0:
    for i in ix:
      tt.add i
    result = (tt, newCall(bindsym"defTensorEq", tt, rhs))
  else:
    result = (tt[0], newCall(bindsym"defTensorEq", tt, rhs))
macro splitLhsDuplicate(n: typed): untyped =
  dbg "splitLhsDuplicate <= ", n, TPLDebug.flow
  # hint ">>>> splitLhsDuplicate <= " & n.treerepr
  # x[a,b] = y[b]
  #  -> x[a.head,b] = y[b]
  #     x[a.tail,b] = x[a.head,b]
  # NOTE: Skip the last stmt in repeated applications of this macro!
  # echo ">>>> splitLhsduplicate: ", n.lisprepr
  # echo "     ", n.repr
  result = n                    # By default.
  let t = n.genDummyTree
  dbg("dummytree:\n" & t.treerepr, lvl = TPLDebug.detail)
  if n.isAutoSumStmt:
    let
      lhs = n.getlhs
      rhs = n[^1]
      lhsT = lhs.indexedTensor
      rhsT = rhs.indexedTensor
      lhsIx = t.branch.getlhsix
      rhsIx = t.branch[^1].idx
      lhsLocalIx = t.idx - rhsIx
      commonIx = lhsIx - lhsLocalIx
    # echo "lhs:        ", lhs.lisprepr
    # echo "lhsLocalIx: ", lhsLocalIx.repr
    dbg("dummytree:lhsT: " & lhsT.lisprepr, lvl = TPLDebug.detail)
    dbg("dummytree:rhsT: " & rhsT.lisprepr, lvl = TPLDebug.detail)
    if lhsLocalIx.len > 0 and rhs.kind in CallNodes and rhsT == newEmptyNode(): # RHS is not a simple tensor.
      if n.kind == nnkAsgn or (n.kind in CallNodes and $n[0] == "[]="):
        var
          stmtHead = n
          lhsTail = newseq[NimNode](lhsLocalIx.len)
        for m in 0..<lhsTail.len:
          lhsTail[m] = lhs
        for n, i in lhsLocalIx:
          let
            ihead = newCall(bindsym"head", i)
            itail = newCall(bindsym"tail", i)
          stmtHead = stmtHead.convert(i, ihead)
          for m in 0..<lhsTail.len:
            if m < n:
              lhsTail[m] = lhsTail[m].convert(i, ihead)
            elif m == n:
              lhsTail[m] = lhsTail[m].convert(i, itail)
            # Else, for m > n, do nothing.
        result = newStmtList().add(stmtHead)
        for c in lhsTail:
          result.add c.wrappedAssign stmtHead.getlhs
      else:
        let (tt, def) = temporaryTensor(commonIx, rhs)
        result = newStmtList(def, n.reAssembleBinOp(lhs, tt))
  dbg "splitLhsDuplicate => ", result, TPLDebug.detail
  # hint "<<<< splitLhsDuplicate => " & result.treerepr
macro splitRhsSum(n: typed): untyped =
  dbg "splitRhsSum <= ", n, TPLDebug.flow
  # echo "\n>>>> splitRhsSum <= ", n.repr
  # hint ">>>> splitRhsSum <= " & n.treerepr
  # x[a] = y[a] `op` z[a,b]
  #  -> x[a] = z[a,b]
  #     x[a] = y[a] `op` x[a]
  # x[a,b] = y[a,c] `op` z[b,d]
  #  -> x[a,b] = y[a,c]
  #     x[a,b] `op`= z[b,d]
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      fun = if n.kind == nnkAsgn: "" else: $n[0]
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhs = n[^1]
      rhsT = t.branch[^1]
      rhsLocalIx = t.idx - lhsIx
      rhsOp = if rhs.kind in CallNodes: $rhs[0] else: ""
    if rhs.kind in CallNodes and rhsOp in autoSumOps:
      if rhs.len == 2:          # Unary op.
        if rhsOp == "+":      # We drop it.
          result = n.copy
          result[^1] = rhs[1]
        elif rhsOp == "-":
          if rhs[1].kind in CallNodes and $rhs[1][0] != "[]":
            if n.kind == nnkAsgn or fun == "[]=": # We reuse the lhs.
              result = newStmtList()
              result.add lhs.wrappedAssign rhs[1]
              result.add lhs.wrappedAssign lhs.prefix "-"
            elif fun == "+=":
              result = n.copy
              result[0] = bindsym"-="
            elif fun == "-=":
              result = n.copy
              result[0] = bindsym"+="
            elif fun in ["*=", "/="]:
              result = n.copy
              result[^1] = rhs[1]
              result = newStmtList(result, lhs.wrappedAssign lhs.prefix "-")
            else:
              error "AutoSum cannot handle: " & n.repr
          else:                 # For simple rhs, we do nothing.
            result = n
        else:
          error "AutoSum only supports unary '+' and '-'.  Received: " & n.repr
      elif rhs.len == 3:        # Binary op of + - * /.
        let
          lop = rhs[1]
          rop = rhs[2]
          lopIx = rhsT.branch[1].idx
          ropIx = rhsT.branch[2].idx
          lopLocalIx = rhsLocalIx - ropIx
          ropLocalIx = rhsLocalIx - lopIx
        if lopLocalIx.len > 0:  # Hit ROP in the next round of recursion.
          result = newStmtList()
          if (n.kind == nnkAsgn or fun == "[]=") and lopIx in lhsIx: # We reuse the lhs.
            result.add(
              n.reAssembleBinOp(lhs, lop),
              infix(lhs, rhsOp & "=", rop)
            )
          else:
            let (tt, def) = temporaryTensor(lopIx - lopLocalIx, lop)
            result.add(
              def,
              n.reAssembleBinOp(lhs, rhs.reAssembleBinOp(tt, rop))
            )
        elif ropLocalIx.len > 0: # Similar to lopLocalIx.len > 0, but we honor order for "*" and "/".
          result = newStmtList()
          if (n.kind == nnkAsgn or fun == "[]=") and ropIx in lhsIx: # We reuse the lhs.
            result.add n.reAssembleBinOp(lhs, rop)
            if rhsOp in ["+", "-"]:
              result.add infix(lhs, rhsOp & "=", lop)
            else:               # Honor the order if not + or -.
              result.add n.reAssembleBinOp(lhs, rhs.reAssembleBinOp(lop, lhs))
          else:
            let (tt, def) = temporaryTensor(ropIx - ropLocalIx, rop)
            result.add(
              def,
              n.reAssembleBinOp(lhs, rhs.reAssembleBinOp(lop, tt))
            )
        else:                   # No local index for both operands
          result = n
      else:
        error "AutoSum only supports unary or binary ops.  Received: " & n.repr
    else:               # RHS is not a call to one of autoSumOps.
      result = n
  else:
    result = n
  # hint "<<<< splitRhsSum => " & result.treerepr
proc conflictTensor(xs: seqset[NimNode], rs: varargs[seqset[NimNode]]): bool =
  # Nodes are BracketExpr(T,...).  Returns true if any
  # tensor/scalar in xs is used in rs with different indices.
  # WARNING: this check is only reliable when auto summation
  # statements have been split.
  proc g(x: NimNode, r: seqset[NimNode]): bool =
    for y in r:
      if x[0] == y[0] and x != y:
        return true
    return false
  # hint "conflictTensor:xs: " & xs.repr
  # hint "conflictTensor:rs: " & rs.repr
  for x in xs:
    for r in rs:
      if x.g r:
        return true
  return false
proc addRequiredTemporary(n: NimNode): NimNode =
  # Note: the conflict resolution is only reliable when this
  # transformation is performed after fully split auto summation.
  # With current implementation, only stmt that isAutoSumStmt are
  # checked.
  result = n                    # By default.
  if n.isAutoSumStmt:
    let
      t = n.genDummyTree
      fun = if n.kind == nnkAsgn: "" else: $n[0]
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhs = n[^1]
      rhsT = t.branch[^1]
      rhsIx = rhsT.idx
      rhsLocalIx = t.idx - lhsIx
      commonIx = rhsIx - rhsLocalIx
      (lhsl, lhsr) = lhs.collectTensors
      (rhsl, rhsr) = rhs.collectTensors
    # hint "Variables in: " & lhs.repr & "\nwith lvalue: " & lhsl.repr & "\nand rest: " & lhsr.repr
    # hint "Variables in: " & rhs.repr & "\nwith lvalue: " & rhsl.repr & "\nand rest: " & rhsr.repr
    if lhsl.conflictTensor(rhsl, rhsr, lhsr) or
       (needAutoSum(n, t) and fun in ["*=", "/="]):
      let (tt, def) = temporaryTensor(commonIx, rhs)
      result = newStmtList().add(def, n.reAssembleBinOp(lhs, tt))
macro requireTemporary*(n: typed): untyped =
  dbg "requireTemporary <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    if n.kind in StmtNodes:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.addRequiredTemporary
  result = n.g
macro splittingHelper(n: typed): untyped =
  # const splits = @[bindsym"splitLhsDuplicate", bindsym"splitRhsSum"]
  template splits(n: untyped): untyped =
    splitRhsSum splitLhsDuplicate n
  proc g(n: NimNode): NimNode =
    # echo "\n## splittingHelper:g <= ", n.treerepr
    if n.kind in StmtNodes:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockStmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n.copy
      result[6] = result[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.copy # We CANNOT modify n because fixpoint use it.
      # if n.kind == nnkInfix and n[0].kind == nnkSym:
      if n.kind in CallNodes:
        # result[0] = ident($result[0])
        result = result.callNodesWrap
      result = getast splits result
    # echo "## splittingHelper:g => ", result.treerepr
  # result = bindsym"splitReqTemp".g bindsym"splitRhsSum".g bindsym"splitLhsDuplicate".g n
  result = n.g
  # hint "## splittingHelper: " & result.treerepr
template splitting*(n: typed): untyped =
  fixpointcall(splittingHelper, n)
proc accumulateAutoSum(n: NimNode): NimNode =
  # echo "\n>>>> accumulateAutoSum <= ", n.treerepr
  let t = n.genDummyTree
  # echo t.treerepr
  if n.needAutoSum t:
    let
      fun = if n.kind == nnkAsgn: "" else: $n[0]
      lhs = n.getlhs
      rhs = n[^1]
      lhsIx = t.branch.getlhsix
      rhsLocalIx = t.idx - lhsIx
    if n.kind == nnkAsgn or fun == "[]=":
      var
        stmtHead = n
        accum = newseq[NimNode](rhsLocalIx.len)
      for m in 0..<accum.len:
        accum[m] = infix(lhs, "+=", rhs)
      for n, i in rhsLocalIx:
        let
          ihead = newCall(bindsym"head", i)
          itail = newCall(bindsym"tail", i)
        stmtHead = stmtHead.convert(i, ihead)
        for m in 0..<accum.len:
          if m < n:
            accum[m] = accum[m].convert(i, ihead)
          elif m == n:
            accum[m] = accum[m].convert(i, itail)
          # Else, for m > n, do nothing.
      result = newStmtList().add(stmtHead)
      for c in accum:
        result.add c
    elif fun in ["*=", "/="]: # Need a temporary.
      error "Internal error: requireTemporary should have dealt with this: " & n.treerepr
    else:                     # += or -= need no special treatment.
      result = n
  else:
    result = n
  # echo "<<<< accumulateAutoSum => ", result.repr
macro autoSum*(n: typed): untyped =
  dbg "autoSum <= ", n, TPLDebug.flow
  # hint ">>>> autoSum <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    if n.kind in StmtNodes:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.accumulateAutoSum
  result = n.g
  dbg "autoSum => ", result, TPLDebug.detail
