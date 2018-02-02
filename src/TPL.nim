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

template tpltemp(n,b:untyped):untyped =
  tplprefix:
    block n:
      b

# Dummy proc symbols; used as tokens for code generation.
# The followings use a trick to create proc with specific types
# that depend on instantiation.
template `[]`*[P0:static[IndexTypeParam]](x:any,
    i0:IndexType[P0]
    ):untyped =
  tpltemp keeplast:
    proc bracket(px,pi0,pp0:any):var elementType(x)
      {.nodecl,tplprefix.} = discard
    tplprefix(bracket(x,i0,i0.Param))
template `[]`*[P0,P1:static[IndexTypeParam]](x:any,
    i0:IndexType[P0],
    i1:IndexType[P1],
    ):untyped =
  tpltemp keeplast:
    proc bracket(px,pi0,pp0,pi1,pp1:any):var elementType(x)
      {.nodecl,tplprefix.} = discard
    tplprefix(bracket(x,i0,i0.Param,i1,i1.Param))

template `[]=`*[P0:static[IndexTypeParam]](x:any,
    i0:IndexType[P0],
    z:any
    ):untyped =
  tpltemp keeplast:
    type E = elementType(x)
    proc bracketeq(px,pi0,pp0:any,pz:E) {.tplprefix.} = discard
    tplprefix(bracketeq(x,i0,i0.Param,z))
template `[]=`*[P0,P1:static[IndexTypeParam]](x:any,
    i0:IndexType[P0],
    i1:IndexType[P1],
    z:any
    ):untyped =
  tpltemp keeplast:
    type E = elementType(x)
    proc bracketeq(px,pi0,pp0,pi1,pp1:any,pz:E) {.tplprefix.} = discard
    tplprefix(bracketeq(x,i0,i0.Param,i1,i1.Param,z))

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

proc has(n:NimNode, k:NimNodeKind):bool =
  for c in n:
    if c.kind == k: return true
  return false

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

proc genloop(n:NimNode, v:seq[NimNode]):NimNode =
  if n.kind == nnkCall and n[0].eqident "TPL:bracketeq":
    # echo n.treerepr
    result = newCall(ident"TPL:loop")
    var v = v
    for i in countup(3,n.len-2,2):
      if n[i].get("kind").intval == 0 and n[i-1] notin v:
        result.add n[i-1]
        v.add n[i-1]
    if result.len == 1:
      result = n.copyNimNode
      for c in n:
        result.add c.genloop v
    else:
      result.add n.copyNimNode
      for c in n:
        result[^1].add c.genloop v
  elif n.kind == nnkCall and n[0].eqident "TPL:bracket":
    # echo n.treerepr
    result = newCall(ident"TPL:loop")
    var v = v
    for i in countup(3,n.len-1,2):
      if n[i].get("kind").intval == 0 and n[i-1] notin v:
        result.add n[i-1]
        v.add n[i-1]
    if result.len == 1:
      result = n.copyNimNode
      for c in n:
        result.add c.genloop v
    else:
      result.add n.copyNimNode
      for c in n:
        result[^1].add c.genloop v
  else:
    result = n.copyNimNode
    for c in n:
      result.add c.genloop v

const AllCallNodes = CallNodes + {nnkConv}

proc liftloop(n:NimNode):NimNode =
  if n.kind in AllCallNodes:
    var shared = newseq[NimNode]()
    for i in 1..<n.len:
      if n[i].kind in CallNodes and n[i][0].eqident "TPL:loop":
        if shared.len == 0:
          for j in 1..<n[i].len-1:
            shared.add n[i][j]
        else:
          var vs = newseq[NimNode]()
          for j in 1..<n[i].len-1:
            if n[i][j] in shared: vs.add n[i][j]
          shared = vs
          if shared.len == 0: break
      else:
        shared.setlen 0
        break
    if shared.len > 0:
      echo "***** ",n.lisprepr
      echo "..... ",shared
      result = newCall(ident"TPL:loop")
      for v in shared: result.add v
      for i in 1..<n.len:
        if n[i].len == shared.len + 2:
          n[i] = n[i][^1].liftloop
        else:
          var ni = n[i].copy
          n[i] = ni.copyNimNode
          n[i].add ni[0]
          for j in 1..<ni.len-1:
            if ni[j] notin shared: n[i].add ni[j]
          n[i].add ni[^1].liftloop
      result.add n
      echo "^^^^^ ",result.lisprepr
    else:
      result = n.copyNimNode
      for c in n:
        result.add c.liftloop
  elif n.kind in {nnkDerefExpr,nnkHiddenDeref} and n.len == 1 and
      n[0].kind in CallNodes and n[0][0].eqident "TPL:loop":
    result = n[0].copyNimNode
    for i in 0..<n[0].len-1: result.add n[0][i]
    result.add n.copyNimNode
    result[^1].add n[0][^1].liftloop
  else:
    result = n.copyNimNode
    for c in n:
      result.add c.liftloop

proc gensum(n:NimNode):NimNode =
  result = n

proc fuse(n:NimNode):NimNode =
  result = n

proc parse(n:NimNode):NimNode =
  echo "----------{ parse"
  # echo n.treerepr
  result = n.genloop(@[]).fixpoint(liftloop).gensum.fixpoint(fuse)
  # echo result.treerepr
  echo "}----------"

proc gencode(n:NimNode):NimNode =
  result = n

macro tpl*(n:typed):untyped {.debug.} =
  result = n.cleanup.cleantpl.parse.gencode.rebuild

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
