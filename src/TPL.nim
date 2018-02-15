import macros
import strutils

macro debug(n:untyped):untyped =
  #echo n.treerepr
  proc pp(nn:NimNode,s,ns:string) =
    var label = " "
    if s.len > 0 or ns.len > 0: label &= "["&s&"::"&ns&"] "
    if nn.kind == nnkSym:
      let ti = nn.gettypeinst
      echo "DEBUG: ",nn.lineinfo,label,nn.lisprepr," : ",ti.lisprepr
      if ti.kind == nnkSym:
        echo "    TYPE: ",ti.symbol.getimpl.lisprepr
    else:
      echo "DEBUG: ",nn.lineinfo,label,nn.lisprepr
    if nn.kind notin AtomicNodes and nn.len > 0:
      echo nn.repr.indent 4
  proc pp(nn:typedesc,s,ns:string) = pp(nn.gettype,s,ns & ":typedesc")
  case n.kind:
  of nnkMacroDef:
    let
      mn = n[0].repr
      gp = n[2]
      fp = n[3]
      bd = n[6]
    # echo mn
    var bd0 = newStmtList quote do:
      echo "----------{ ",`mn`
    for i in 0..<gp.len:
      for j in 0..<gp[i].len-2:
        if gp[i][^2].kind != nnkStaticTy: continue
        let
          g = gp[i][j]
          t = gp[i][^2][0].repr
          li = g.lineinfo
          rp = g.repr
        bd0.add quote do:
          echo "DEBUG: ",`li`," [",`mn`,"::",`rp`,"] ",`g`," : ",`t`
    for i in 1..<fp.len:
      for j in 0..<fp[i].len-2:
        if fp[i][^2].kind == nnkStaticTy: continue
        bd0.add newcall(bindsym"pp",fp[i][j],mn.newLit,fp[i][j].repr.newLit)
    # echo fp.lisprepr
    bd0 = newBlockStmt(ident"debug-pre",bd0)
    var bd1 = newStmtList newcall(bindsym"pp",ident"result",mn.newLit,"result".newLit)
    bd1.add quote do:
      echo "}----------"
    bd1 = newBlockStmt(ident"debug-post",bd1)
    if bd.kind == nnkStmtList:
      bd.insert 0,bd0
      bd.add bd1
    else:
      n[6] = newStmtList(bd0,bd,bd1)
    # echo bd.lisprepr
    result = n
  else:
    let nr = n.repr
    result = newcall(bindsym"pp",n,"".newLit,nr.newLit)
  #echo result.repr

type
  IndexTypeParam = object
    kind: int
    id: int
    len: int
    bound: int
    stride: int
  IndexType[Param:static[IndexTypeParam]] = distinct int
  LayoutParam = object
    id: int
    index: IndexTypeParam
  TensorTypeParam = object
    elementType: NimNode
    indices: seq[IndexTypeParam]
    layout: seq[LayoutParam]

proc tensorType(n:NimNode):TensorTypeParam =
  # echo n.gettypeinst.treerepr
  let t = n.gettypeinst
  result.indices.newseq 0
  result.layout.newseq 0
  var tt = t
  while tt.kind == nnkBracketExpr and tt[0].eqident "array":
    var it: IndexTypeParam
    it.id = -1
    it.stride = 1
    if tt[1].kind == nnkInfix and tt[1].len == 3:
      it.bound = tt[1][1].intval.int
      it.len = 1 + tt[1][2].intval.int - tt[1][1].intval.int
      result.indices.add it
    else:
      error "Unknown input: " & tt.treerepr &
        "\nReceived: " & n.repr & "\nType: " & t.treerepr
    tt = tt[2]
  if tt.kind != nnkSym:
    error "Unknown input: " & tt.treerepr &
      "\nReceived: " & n.repr & "\nType: " & t.treerepr
  result.elementType = tt
  # echo result

proc get(n:NimNode, s:string):NimNode =
  if n.kind != nnkObjConstr:
    error "Unknown input: " & n.treerepr
  for i in 1..<n.len:
    if n[i].kind != nnkExprColonExpr or n[i].len != 2:
      error "Unknown input: " & n[i].treerepr &
        "\nReceived: " & n.treerepr
    if n[i][0].eqident s: return n[i][1]
  error "Unknown input: " & n.treerepr & "\nWith s: " & s

proc indexType(n:NimNode):seq[IndexTypeParam] =
  # echo n.treerepr
  result.newseq n.len
  for i in 0..<n.len:
    result[i].kind = n[i].get("kind").intval.int
    result[i].id = n[i].get("id").intval.int
    result[i].len = n[i].get("len").intval.int
    result[i].bound = n[i].get("bound").intval.int
    result[i].stride = n[i].get("stride").intval.int

proc indexingResultType(t:TensorTypeParam,
    i:varargs[IndexTypeParam]):NimNode =
  # echo t
  # for k in 0..<i.len: echo i[k]
  var matched = newseq[int]()
  for k in 0..<i.len:
    var m = -1
    for j in 0..<t.indices.len:
      if j in matched: continue
      if t.indices[j].id < 0 or t.indices[j].id == i[k].id:
        let
          tl = t.indices[j].bound
          th = t.indices[j].bound + t.indices[j].stride * (t.indices[j].len - 1)
          il = i[k].bound
          ih = i[k].bound + i[k].stride * (i[k].len - 1)
        if il < tl or ih > th:
          error "Index out of bound " & $i[k] & " for tensor " & $t
        m = j
        break
    if m < 0:
      error "Cannot match index " & $i[k] & " for tensor " & $t
    else:
      matched.add m
  if matched.len == t.indices.len:
    result = t.elementType
  else:
    var es = "Cannot indexing\n" & $t & "\nwith"
    for k in 0..<i.len: es &= "\n" & $k & " : " & $i[k]
    error  es

macro tplType(x:typed,ix:typed):untyped {.debug.} =
  var
    tt = tensorType x
    it = indexType ix
  result = indexingResultType(tt,it)

macro tplNew(x:typedesc):untyped {.debug.} =
  if x.gettype[1].eqident "float":
    result = newLit(0.0)
  else:
    error "tplNew: not implemented for '" & $x.gettype & "'"

#template tplNew(x:typed,it:varargs[IndexTypeParam]):untyped =
#  type T = tplType(x,it)
#  tplNew(T)

macro elementType(x:typed):untyped {.debug.} =
  var tt = tensorType x
  result = tt.elementType

macro tplprefix(n:untyped):untyped =
  var n = n
  if n.kind == nnkStmtList and n.len == 1:
    n = n[0]
  if n.kind in RoutineNodes:
    result = n
    result.name = ident("TPL:" & $result.name)
  elif n.kind in CallNodes + {nnkBlockStmt}:
    result = n
    result[0] = ident("TPL:" & $result[0])
  else:
     error "Unimplemented for " & n.lisprepr

proc newtpl(s:string, lineInfoFrom:NimNode=nil):NimNode =
  newNimNode(nnkCall, lineInfoFrom).add ident("TPL:"&s)

proc istpl(n:NimNode,s:string):bool =
  n.kind == nnkCall and n[0].eqident("TPL:"&s)

template tpltemp(n,b:untyped):untyped =
  tplprefix:
    block n:
      b

# Dummy proc symbols; used as tokens for code generation.
#proc index[P:static[IndexTypeParam]](
#  i:IndexType[P],p:static[IndexTypeParam]):int {.nodecl,tplprefix.} = discard
proc index(i,p:any):int {.nodecl,tplprefix.} = discard

# The followings use a trick to create proc with specific types
# that depend on instantiation.
template `[]`*[P0:static[IndexTypeParam]](x:any,
    i0:IndexType[P0]
    ):untyped =
  tpltemp keeplast:
    type R = tplType(x, [i0.Param])
    proc bracket(px,pi0:any):var R {.nodecl,tplprefix.} = discard
    tplprefix(bracket(x,
      tplprefix(index(i0,i0.Param))))
template `[]`*[P0,P1:static[IndexTypeParam]](x:any,
    i0:IndexType[P0],
    i1:IndexType[P1],
    ):untyped =
  tpltemp keeplast:
    type R = tplType(x, [i0.Param,i1.Param])
    proc bracket(px,pi0,pi1:any):var R {.nodecl,tplprefix.} = discard
    tplprefix(bracket(x,
      tplprefix(index(i0,i0.Param)),
      tplprefix(index(i1,i1.Param))))

template `[]=`*[P0:static[IndexTypeParam]](x:any,
    i0:IndexType[P0],
    z:any
    ):untyped =
  tpltemp keeplast:
    type R = tplType(x, [i0.Param])
    proc bracket(px,pi0:any):var R {.nodecl,tplprefix.} = discard
    tplprefix(bracket(x,
      tplprefix(index(i0,i0.Param)))) = z
template `[]=`*[P0,P1:static[IndexTypeParam]](x:any,
    i0:IndexType[P0],
    i1:IndexType[P1],
    z:any
    ):untyped =
  tpltemp keeplast:
    type R = tplType(x, [i0.Param,i1.Param])
    proc bracket(px,pi0,pi1:any):var R {.nodecl,tplprefix.} = discard
    tplprefix(bracket(x,
      tplprefix(index(i0,i0.Param)),
      tplprefix(index(i1,i1.Param)))) = z

proc cleantpl(n:NimNode):NimNode =
  var n = n
  if n.kind in {nnkBlockStmt,nnkBlockExpr} and n[0].eqident "TPL:keeplast":
    if n.len == 2 and n[1].kind in {nnkStmtList,nnkStmtListExpr}: n = n[1][^1]
    else: error "Unknow input " & n.treerepr
  result = n.copyNimNode
  for c in n: result.add c.cleantpl

import metatools

var IndexID {.compileTime.} = 0
macro Index*(length,bound,stride:typed):untyped =
  template newIndex(nid,length,bnd,srd) =
    const P = IndexTypeParam(kind:0, id:nid, len:length, bound:bnd, stride:srd)
    IndexType[P]
  let nid = newLit IndexID
  result = getAst(newIndex(nid,length,bound,stride))
  IndexID.inc

proc replace(n,x,y:NimNode):NimNode =
  if n == x:
    result = y.copy
  else:
    result = n.copyNimNode
    for c in n:
      result.add c.replace(x,y)

proc has(n:NimNode, k:NimNodeKind):bool =
  for c in n:
    if c.kind == k: return true
  return false

proc contains(n,item:NimNode):bool =
  result = false
  for c in n:
    if c == item:
      result = true
      break

proc cleanup*(n:NimNode):NimNode =
  ## This cleans up typed AST, makes the AST easier to work with.
  ## This is similar to `rebuild`, but without stripping type info.

  # Special node kinds have to be taken care of.
  if n.kind in nnkCallKinds and n[^1].kind == nnkBracket and
       n[^1].len>0 and n[^1].has(nnkHiddenCallConv):
    # special case of varargs
    result = n.copyNimNode
    for i in 0..<n.len-1: result.add n[i].cleanup
    for c in n[^1]:
      if c.kind == nnkHiddenCallConv: result.add c[1].cleanup
      else: result.add c.cleanup
  elif n.kind in nnkCallKinds and n[0].eqident("echo") and n.len>0 and n[1].kind == nnkBracket:
    # One dirty hack for the builtin echo, with no nnkHiddenCallConv (this is been caught above)
    result = n.copyNimNode
    result.add n[0]
    for c in n[1]: result.add c.cleanup
  elif n.kind in nnkCallKinds and n[^1].kind == nnkHiddenStdConv and n[^1][1].kind == nnkBracket and
       n[^1][1].len>0 and n[^1][1].has(nnkHiddenCallConv):
    # Deals with varargs
    result = n.copyNimNode
    result.add n[0]
    for i in 1..<n.len-1: result.add n[i].cleanup
    for c in n[^1][1]:
      if c.kind == nnkHiddenCallConv: result.add c[1].cleanup
      else: result.add c.cleanup
  elif n.kind == nnkHiddenStdConv:
    # Generic HiddenStdConv
    result = n[1].cleanup
  elif n.kind == nnkHiddenAddr and n[0].kind == nnkHiddenDeref:
    result = n[0][0].cleanup
  elif n.kind == nnkHiddenDeref and n[0].kind == nnkHiddenAddr:
    result = n[0][0].cleanup
  elif n.kind == nnkTypeSection:
    # Type section is special.  Once the type is instantiated, it exists, and we don't want duplicates.
    result = newNimNode(nnkDiscardStmt,n).add(newStrLitNode(n.lisprepr))

  # Cleanup for other kinds
  else:
    result = n.copyNimNode
    for c in n:
      result.add c.cleanup

var TPLMaxRec {.compileTime.} = 100
proc fixpoint(n:NimNode, f:proc):NimNode =
  echo "----------{ fixpoint <"
  echo n.repr
  echo ">"
  var
    j = 0
    n = n
    nn = f(n.copy)
  while nn != n:
    echo "#### fixpoint ",j," ["
    echo nn.repr
    echo "]"
    if j > TPLMaxRec: error "Max recursion limit reached for:\n" & n.treerepr
    n = nn.copy
    nn = f(nn)
    j.inc
  result = nn
  echo "< result"
  echo result.repr
  echo ">}----------"

type LoopAST = object  ## Each node in loop is an nnkPar.
  node: NimNode  ## The original NimNode.
  loop: NimNode  ## The same structure as node, but contains loop vars.
  param: NimNode  ## A list of pairs of a loop var and its parameter.

proc initLoopAST(n:NimNode):LoopAST =
  proc f(n:NimNode):NimNode =
    result = newpar()
    for c in n:
      result.add c.f
    result.add newpar()  # The extra nnkpar is for loop variables
  result.node = n
  result.loop = n.f
  result.param = newpar()
proc len(n:LoopAST):int = n.node.len
proc kind(n:LoopAST):NimNodeKind = n.node.kind
proc `[]`(n:LoopAST,i:int):LoopAST =
  result.node = n.node[i]
  result.loop = n.loop[i]
  result.param = n.param
proc vars(n:LoopAST):NimNode = n.loop[^1]
proc `vars=`(n:LoopAST,v:NimNode) = n.loop[^1] = v
iterator items(n:LoopAST):LoopAST =
  var i = 0
  while i < n.len:
    yield n[i]
    i.inc

proc createLoops(n:NimNode):LoopAST =
  proc f(ast:LoopAST) =
    let n = ast.node
    if n.istpl"bracket":
      for i in 2..<n.len:
        if not n[i].istpl"index":
          var s = "Unexpected: " & n[i].lisprepr
          s &= "\nElement " & $i & " of: " & n.repr
          error s
        if n[i][2].get("kind").intval == 0:
          if n[i][1] notin ast.vars: ast.vars.add n[i][1]
          var absent = true
          for p in ast.param:
            if p[0] == n[i][1]:
              absent = false
              break
          if absent:
            ast.param.add newpar(n[i][1], n[i][2])
    for c in ast: c.f
  result = n.initLoopAST
  result.f

var
  SumBoundaryProcs* = @["+", "-", "*", "/", "*=", "/="]
    ## We will not lift loops above the tree of the call nodes with the
    ## listed procedures (in addition to the `nnkAsgn` node), if the
    ## loop variables of the automatic loops are not shared among
    ## the arguments of the procedures.
  SumBoundaryExceptionArgs* = @[
    ("*=", @[1]),
    ("/=", @[1])
    ]
    ## For those procs in `SumBoundaryProcs`, we make exceptions for
    ## some arguments, specified with the index of the NimNode, such
    ## that any loops of those arguments will be lifted to be loops of
    ## the call node.

const
  LoopBoundaryNodes = {nnkStmtList,nnkStmtListExpr}  # Need more here.
  AllCallNodes = {nnkConv} + CallNodes
  SumNodes = AllCallNodes + {nnkAsgn}  # Sum loops that are their children

proc collectLoops(n:LoopAST) =
  ## Depth first; collecting loop variables from lower branches.
  for c in n: c.collectLoops
  if n.kind in LoopBoundaryNodes: return
  for c in n:
    for v in c.vars:
      if v notin n.vars:
        n.vars.add v

proc cleanSumBoundary(n:LoopAST) =
  ## Width first; remove non-shared loop variables for
  ## `SumBoundaryProcs` and `nnkAsgn`.
  var isSumBoundary = n.kind == nnkAsgn
  if (not isSumBoundary) and n.kind in AllCallNodes:
    for p in SumBoundaryProcs:
      if n.node[0].eqident p:
        isSumBoundary = true
        break
  if isSumBoundary:
    # Remove non-loops loop variables.
    # Skip the 0th node if we are in `AllCallNodes`
    let skip = if n.kind in AllCallNodes: 1 else: 0
    var loops = n[skip].vars.copy  # copy is important
    for i in skip+1..<n.len:
      var t = newpar()
      for v in loops:
        if v in n[i].vars: t.add v
      loops = t
    if n.kind == nnkAsgn:
      for v in n[0].vars:
        if v notin loops:
          loops.add v
    else:
      for e in SumBoundaryExceptionArgs:
        if n.node[0].eqident e[0]:
          for i in e[1]:
            for v in n[i].vars:
              if v notin loops:
                loops.add v
    for i in countdown(n.vars.len-1,0):
      if n.vars[i] notin loops:
        n.vars.del i
  for c in n: c.cleanSumBoundary

proc cleanLoops(n:LoopAST) =
  ## Clean redundent loops that were left over by `collectLoops`.
  proc f(n:LoopAST,vs:NimNode) =
    # `vs` collects loop vars from the tree trunk.
    var vs = vs.copy
    for i in countdown(n.vars.len-1,0):
      if n.vars[i] in vs:
        n.vars.del i
      else:
        vs.add n.vars[i]
    for c in n: c.f vs
  n.f newpar()

proc genNode(n:LoopAST):NimNode =
  ## Add loop or sum nodes with loop variables.
  result = n.node.copyNimNode
  for c in n:
    var branch = c.genNode
    if c.vars.len > 0:
      var loop:NimNode
      if n.kind in SumNodes:
        loop = newtpl("sumReturn",branch)
        loop.add newtpl("sumvar",branch)
        loop[1].add branch.gettypeinst
      else:
        loop = newtpl("loop",branch)
      for v in c.vars:
        var i = 0
        while i < c.param.len:
          # echo v,"  =?=  ",c.param[i].repr
          if c.param[i][0] == v: break
          i.inc
        if i >= c.param.len:
          var s = "Cannot find loop var: " & v.repr
          s &= "\nFor node: " & c.node.repr
          s &= "\nKnown vars: " & c.param.repr
          error s
        loop.add c.param[i]
      loop.add branch
      # echo "#### ",loop.repr
      branch = loop
    result.add branch
  if result.kind == nnkAsgn and result[1].istpl"sumReturn":
    var r = newtpl("sumAsgn",result[1])
    r.add result[0]
    for i in 2..<result[1].len:
      r.add result[1][i]
    result = r

proc fuse(n:NimNode):NimNode =
  # FIXME
  result = n

proc gencode(n:NimNode):NimNode =
  # FIXME
  result = n

proc genloopsum(n:NimNode):NimNode =
  echo "----------{ genloopsum"
  # echo n.treerepr
  var loopast = n.createLoops
  loopast.collectLoops
  loopast.cleanSumBoundary
  loopast.cleanLoops
  result = loopast.genNode
  # echo result.treerepr
  echo "}----------"

macro tpl*(n:typed):untyped {.debug.} =
  result = n.cleanup.cleantpl.genloopsum.fixpoint(fuse).gencode.rebuild

when isMainModule:
  tpl:
    const
      L = 3
      M = 2
    type
      I = Index(L,0,1) # Index(L,B,S)
      J = Index(M,0,1)
    var
      X,Y:array[L,float]
      A:array[M,array[L,float]]
      Z:array[M,float]
      m:float
      a:I
      b:J
    X[a] = 1
    Y[a] = a.float
    X[a] += Y[a]
    A[b,a] = b.float + 0.001 * a.float
    echo A[b,a]
    Z[b] = A[b,a] * X[a]
    m = Z[b]
    echo Z[b]
    echo m
    m = Z[b] * A[b,a] * X[a]
    echo m
