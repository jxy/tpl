import macros,strutils
import seqset,indexTypes

const StmtNodes* = {nnkStmtList, nnkStmtListExpr}

const autoSumFunctions* = ["=", "+=", "-=", "*=", "/=", "[]="]
const autoSumFunctionNoBracket* = ["=", "+=", "-=", "*=", "/="]
const autoSumOps* = ["+", "-", "*", "/"]

import debug

iterator pairs*(n: NimNode): (int, NimNode) =
  for i in 0..<n.len:
    yield(i, n[i])
proc unwrap*(n: NimNode): NimNode =
  result = n
  while result.kind in {nnkPar, nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv}:
    result = if result.kind == nnkHiddenStdConv: result[1] else: result[0]

proc wrappedAssign*(lhs, rhs: NimNode): NimNode =
  if lhs.kind == nnkBracketExpr:
    for i in 0..<lhs.len:
      lhs[i] = lhs[i].newPar
  result = newAssignment(lhs, rhs.newPar)

proc rebindIndexing*(n: NimNode): NimNode =
  if $n[0] == "[]":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len:
      result.add n[i].unwrap.newPar
  elif $n[0] == "[]=":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len-1:
      result.add n[i].unwrap.newPar
    result = result.wrappedAssign n[^1]
  else:
    result = n

proc callNodesWrap*(n: NimNode): NimNode =
  # hint "callNodesWrap <= " & n.treerepr
  result = n
  if result[^1].kind == nnkHiddenStdConv:
    let nn = result[^1][1].copy
    if nn.kind == nnkBracket:   # A vararg
      result.del(result.len-1)
      for c in nn:
        if c.kind == nnkHiddenCallConv:
          result.add c[1]
        else:
          result.add c
    else:
      result[^1] = nn
  if result.len > 1:
    for i in 1..<result.len:
      if result[i].kind notin AtomicNodes + {nnkPar}:
        result[i] = unwrap(result[i]).newPar
  # hint "callNodesWrap => " & result.treerepr

proc replace*(n: NimNode, i: NimNode, j: NimNode): NimNode =
  # echo "\n>>>> replace"
  # echo n.lisprepr
  # echo i.lisprepr
  # echo j.lisprepr
  if n == i:
    result = j
  else:
    result = n.copyNimNode
    for c in n:
      result.add c.replace(i,j)
  # echo result.lisprepr
  # echo "<<<< replace"
proc convert*(n: NimNode, i: NimNode, j: NimNode): NimNode =
  # echo "\n>>>> convert"
  # echo n.treerepr
  # echo i.treerepr
  # echo j.treerepr
  proc go(n: NimNode, i: NimNode, j: NimNode): tuple[rep: bool, nn: NimNode] =
    # echo "  ==== go ENTER:n: ", n.lisprepr
    if n == i:
      # echo "  ---- n == i"
      result = (true, j)
    else:
      result.rep = false
      # echo "       n: ", n.treerepr
      # result.nn = n.copyNimNode # SIGSEGV?!
      result.nn = n.copy
      # echo "THE node: ", result.nn.lisprepr
      for c in 0..<n.len:
        let cc = n[c].go(i,j)
        # echo "  ---- ", cc.rep, " : ", cc.nn.lisprepr
        # echo "BEFORE"
        # result.nn.add cc.nn
        # echo "AFTER"
        # echo "## ", result.rep, " : ", result.nn.lisprepr
        if cc.rep:
          result.rep = true
          result.nn[c] = cc.nn
    #[
    if result.nn.kind == nnkHiddenAddr:
      # we may not need this, but just keep this kind here
      # just in case something breaks because of nnkHiddenAddr.
      result.nn = result.nn[0]
    ]#
    # The compiler wouldn't simply do the call conv again.
    # if result.nn.kind == nnkHiddenCallConv:
    #   # simply ask the compiler to do the call conv again
    #   result.nn = result.nn[1]
    # echo "## ", result.rep, " : ", result.nn.lisprepr
    if result.rep:
      if result.nn.kind == nnkHiddenCallConv:
        result.nn = result.nn[1]
      elif result.nn.kind in CallNodes:
        result.nn = result.nn.callNodesWrap.rebindIndexing
        # Make every sym ident would break generic function definitions.
        # result.nn[0] = ident($result.nn[0].symbol)
        # Limiting to indexing op only, may break with other replacment.
      # elif result.nn.kind in {nnkHiddenDeref, nnkHiddenAddr}:
      #   result.nn = if result.nn[0].kind == nnkPar: result.nn[0] else: result.nn[0].newPar
      elif result.nn.kind == nnkConv:
        # Deals with explicit converter, such as `int`, `float`.
        # echo result.nn.treerepr
        # result.nn[0] = ident($result.nn[0])
        var nnn = newCall(ident($result.nn[0].symbol))
        for i in 1..<result.nn.len:
          nnn.add result.nn[i]
        result.nn = nnn
    # echo "       repl : ", result.rep
    # echo "       node : ", result.nn.lisprepr
    # echo "  **** go LEAVE:n: ", n.lisprepr
  result = go(n,i,j).nn
  # echo result.treerepr
  # echo "<<<< convert"
proc staticint*(x: NimNode): int =
  int(intVal(if x.kind == nnkSym: x.symbol.getImpl else: x))
macro unrollfor*(i: untyped, lo, hi: int, n: untyped): stmt =
  # echo "\n>>>> unrollfor"
  # echo n.treerepr
  result = newStmtList()
  let
    ll = staticint lo
    hh = staticint hi
  for j in ll..hh:
    result.add(n.replace(i, newLit(j)))
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< unrollfor"

proc dummyStr*(n: NimNode): string =
  let s = n.repr.strip
  var id = newString(s.len)
  var j = 0
  for i in 0..<s.len:
    if s[i] in IdentChars - {'_'} + {'-'}:
      id[j] = s[i]
      inc j
    elif j > 0 and id[j-1] != '_':
      id[j] = '_'
      inc j
  if id[j-1] == '_':
    dec j
  if j != s.len:
    id.setLen j
  return id

proc delete*[T](s: var seq[T], x: T) =
  for i, c in s:
    if c == x:
      s.delete i

macro fixpoint(i: static[int], m, oldn, n: typed): untyped =
  # Call m repeatedly on n until nothing changes, with each step
  # type checked.  Requires m accepting a typed.
  dbg "fixpoint:" & $m & ":" & $i & " => ", n, TPLDebug.flow
  if i == 0 or oldn != n:
    result = newCall(bindsym"fixpoint", newLit(i+1), m, n, newCall(m, n))
  else:
    result = n
template fixpointcall*(m, n: typed): untyped =
  fixpoint(0, m, newEmptyNode(), n)

proc collectTensors*(n: NimNode): (seqset[NimNode], seqset[NimNode]) =
  # Returns tensors or scalars in the form of Par(BracketExpr())
  # in two lists: those used as lvalues and those did not.  Note:
  # scalars (symbol not indexed with []) are only returned when
  # they are used as a var (lvalue).
  # echo "collectTensors:n <= # ", n.lisprepr
  proc extractIndex(n: NimNode): NimNode =
    if n.kind in CallNodes and $n[0] == "indexValue":
      result = n[1].extractIndex
    elif n.kind in CallNodes and $n[0] == "TPLDummyConv":
      result = n[1].extractIndex
    else:
      result = n
  proc extractTensor(n: NimNode): NimNode =
    if n.kind == nnkDotExpr and $n[1] == "data":
      result = n[0].extractTensor
    elif n.kind == nnkDerefExpr:
      result = n[0].extractTensor
    elif n.kind == nnkStmtListExpr:
      # FIXME: I cannot think of a reliable way to protect against data race here.
      result = n[^1].extractTensor
    else:
      result = n
  var lv, vl: seqset[NimNode]
  lv.init
  vl.init
  template recurseAdd(nn: NimNode): untyped =
    let (a, b) = nn.collectTensors
    for x in a:
      lv.incl x
    for x in b:
      vl.incl x
  if n.kind == nnkAsgn:
    var nn = n[0].unwrap
    if nn.kind == nnkSym:    # scalar
      lv.incl newNimNode(nnkBracketExpr).add nn
      recurseAdd n[1]
    elif nn.kind == nnkBracketExpr and nn[0].kind == nnkSym:    # array
      var t = newNimNode(nnkBracketExpr).add nn[0]
      for m in 1..<nn.len:
        t.add nn[m].extractIndex
      lv.incl t
    else:
      error "Don't know how to extract tensors from: " & nn.treerepr & "\nin: " & n.treerepr
  elif n.kind in CallNodes:
    if n[0].kind == nnkSym:
      # echo "collectTensors:n: ", n.repr
      var fp = n[0].symbol.getimpl[3]
      # echo "collectTensors:fp: ", fp.repr
      # if fp[0].kind == nnkVarTy: # Return a var (lvalue).
      #   error "what do we do here?"
      var k = 1
      for i in 1..<fp.len:            # List of params.
        let isVarParam = fp[i][^2].kind == nnkVarTy
        for j in 0..<fp[i].len-2:
          var nkj = n[k+j].unwrap
          let errmsg = "Don't know how to extract tensors from: " &
            n.treerepr & "\nwith: " & fp.treerepr &
            "\nlooking at: " & nkj.treerepr
          if nkj.kind in CallNodes + {nnkConv, nnkStmtListExpr, nnkTypeOfExpr}:    # TypeOfExpr shouldn't be here (bug in type resolution?)
            # Don't care.
            recurseAdd nkj
          elif nkj.kind in {nnkSym, nnkDotExpr, nnkDerefExpr}:
            var t = newNimNode(nnkBracketExpr)
            # Add the tensor symbol.
            t.add nkj.extractTensor
            # Add indices.
            if i == 1: # The first argument to [] or []= is the tensor.
              if $n[0] == "[]":
                for m in 2..<n.len:
                  t.add n[m].extractIndex
              if $n[0] == "[]=":
                for m in 2..<n.len-1:
                  t.add n[m].extractIndex
            if isVarParam:
              lv.incl t
            else:
              vl.incl t
          elif nkj.kind in nnkLiterals or
               (nkj.kind == nnkBracketExpr and
                nkj[0].kind == nnkSym and
                $nkj[0].gettype[0] == "typeDesc"):
            discard "We don't need to worry about these."
          elif nkj.kind == nnkBracketExpr:
            var nn = nkj[0]
            while nn.kind == nnkBracketExpr:
              nn = nn[0]
            if nn.kind == nnkSym:
              if nn.symbol.getimpl.kind == nnkBracket:
                discard "It may be an array constant.  Ignore."
              else:
                var t = newNimNode(nnkBracketExpr).add nn
                var nnn = nkj
                while nnn.kind == nnkBracketExpr:
                  for m in 1..<nnn.len:
                    t.insert(m,nnn[m].extractIndex)
                  nnn = nnn[0]
            else:
              error errmsg
          elif nkj.kind in {nnkIfExpr,nnkBracket}:
            for c in nkj:
              recurseAdd c
          else:
            error errmsg
        k.inc(fp[i].len-2)
    else:
      error "Don't know how to extract tensors from: " & n.treerepr
  elif n.kind == nnkBracketExpr:
    var t = n.copy
    for i in 1..<t.len:
      t[i] = t[i].extractIndex
    if n[0].kind in {nnkHiddenAddr, nnkHiddenDeref} and
       n[0][0].kind in {nnkSym, nnkDotExpr, nnkDerefExpr}:
      # WARNING: this check may no longer work if getlhs removes these hidden nodes.
      t[0] = t[0][0].extractTensor
      lv.incl t
    elif n[0].kind in {nnkSym, nnkDotExpr}:
      t[0] = t[0].extractTensor
      vl.incl t
    elif n[0].kind in CallNodes:
      t[0] = t[0].extractTensor
      var fp = n[0][0].symbol.getimpl[3]
      if fp[0].kind == nnkVarTy: # Return a var (lvalue).
        lv.incl t
      else:
        vl.incl t
      for c in n[0]:
        recurseAdd c
    else:
      var nn = n[0]
      while nn.kind == nnkBracketExpr:
        nn = nn[0]
      if nn.kind == nnkSym:
        if nn.symbol.getimpl.kind == nnkBracket:
          discard "It may be an array constant.  Ignore."
        else:    # array
          t = newNimNode(nnkBracketExpr).add nn
          var nnn = n
          while nnn.kind == nnkBracketExpr:
            for m in 1..<nnn.len:
              t.insert(m,nnn[m].extractIndex)
            nnn = nnn[0]
            lv.incl t    # Impossible to see if it's an lvalue.
      else:
        error "Don't know how to extract tensors from: " & n.treerepr
  else:
    for c in n:
      recurseAdd c
  result = (lv, vl)
  # echo "collectTensors:result => ", result.repr
proc indexedTensor*(m: NimNode): NimNode =
  var n = m.unwrap
  if n.kind in CallNodes and $n[0] in ["[]", "[]="]:
    result = n[1]
  elif n.kind == nnkBracketExpr:
    result = n[0]
  else:                         # What if a HiddenAddr?
    result = newEmptyNode()
type
  dummyTree* = object
    idx*: seqset[NimNode]
    branch*: seq[dummyTree]
proc genDummyTree*(n: NimNode): dummyTree =
  # echo "\n>>>> genDummyTree"
  # echo n.treerepr
  proc skipDummyCheck(n: NimNode, i: int): bool =
    # result = n.kind notin CallNodes + {
    #   nnkStmtList, nnkBlockStmt, nnkBracket,
    #   nnkIfStmt, nnkWhenStmt, nnkCaseStmt, nnkWhileStmt, nnkTryStmt,
    #   nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv
    # }
    result = n.kind in {nnkConstSection, nnkVarSection, nnkLetSection}
    result = result or n.kind == nnkForStmt and i < 2 # We check only the body.
    # if result:
    #   echo "skipDummyCheck ", i, " ", n.lisprepr
    #   echo "    => ", result
  proc g(n: NimNode): dummyTree =
    result.idx.init
    newseq result.branch, n.len
    let d = n.dummyFromConverter
    if d.kind != nnkNilLit:
      # echo "   result.idx: ", result.idx.repr
      # echo "-- dummy: ", n.lisprepr
      result.idx.incl d
      # echo "   result.idx: ", result.idx.repr
    else:
      # echo "subtree result.idx: ", result.idx.repr
      for i, c in n:
        let t = if n.skipDummyCheck i: newEmptyNode().g else: c.g
        result.idx += t.idx
        # echo "     += ", t.idx.repr
        # echo "        result.idx: ", result.idx.repr
        result.branch[i] = t
      # echo "subtree result.idx: ", result.idx.repr
  result = n.g
  # echo "<<<< genDummyTree =>\n", result.treerepr
proc getlhsix*(s: seq[dummyTree]): seqset[NimNode] =
  result.init
  for i in 0..<s.len-1: # Every but last belongs to the left hand side.
    result.incl s[i].idx
proc getrhsix*(s: seq[dummyTree]): seqset[NimNode] =
  result.init
  if s.len > 0:
    result.incl s[^1].idx
proc isAutoSumStmt*(n: NimNode): bool =
  result = n.kind == nnkAsgn or (n.kind in CallNodes and $n[0] in autoSumFunctions)
proc getlhs*(n: NimNode): NimNode =
  # echo "getlhs: ", n.treerepr
  if n.kind == nnkAsgn:
    result = n[0]
  elif n.kind in CallNodes and $n[0] in autoSumFunctionNoBracket and n.len == 3:
    result = n[1]
  elif n.kind in CallNodes and $n[0] == "[]=":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len-1:
      result.add n[i]
  else:
    error "Failed to get the LHS of NimNode:\n" & n.treerepr
proc reAssembleBinOp*(n, lhs, rhs: NimNode): NimNode =
  if n.kind == nnkAsgn or
     (n.kind in CallNodes and $n[0] == "[]=" and lhs.kind == nnkBracketExpr):
    result = wrappedAssign(lhs, rhs)
  elif n.kind in CallNodes and n.len == 3:
    result = n.copyNimNode.add(n[0], lhs, rhs.newPar)
    result = result.callNodesWrap
  else:
    error "Don't know how to reassemble binary op for\n" &
      n.repr & "\nfrom lhs\n" & lhs.repr & "\nand rhs\n" & rhs.repr
