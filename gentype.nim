import macros
import strutils
import math

iterator pairs(n: NimNode): (int, NimNode) =
  for i in 0..<n.len:
    yield(i, n[i])
proc replace(n: NimNode, i: NimNode, j: NimNode): NimNode =
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
proc convert(n: NimNode, i: NimNode, j: NimNode): NimNode =
  # echo "\n>>>> convert"
  # echo n.treerepr
  # echo i.treerepr
  # echo j.treerepr
  proc go(n: NimNode, i: NimNode, j: NimNode): tuple[rep: bool, nn: NimNode] =
    # echo "  ==== go : ", n.lisprepr
    if n == i:
      # echo "  ---- n == i"
      result = (true, j)
    else:
      # echo "A"
      result.rep = false
      # echo "* n: ", n.lisprepr
      result.nn = n.copy # Sometimes we need to copy before copyNimNode???
      result.nn.del(0, n.len) # We just copy it and delete its children.
      # echo "THE node: ", result.nn.lisprepr
      # result.nn = n.copyNimNode # FIXME: we may not need the changes later if we stop using copyNimNode.
      # echo "THE node: ", result.nn.lisprepr
      for c in n:
        let cc = c.go(i,j)
        # echo "# ", cc.rep, " : ", cc.nn.lisprepr
        # echo "BEFORE"
        result.nn.add cc.nn
        # echo "AFTER"
        # echo "## ", result.rep, " : ", result.nn.lisprepr
        if cc.rep:
          result.rep = true
    #[
    if result.nn.kind == nnkHiddenAddr:
      # we may not need this, but just keep this kind here
      # just in case something breaks because of nnkHiddenAddr.
      result.nn = result.nn[0]
    ]#
    if result.nn.kind == nnkHiddenCallConv:
      # simply ask the compiler to do the call conv again
      result.nn = result.nn[1]
    # echo "## ", result.rep, " : ", result.nn.lisprepr
    if result.rep:
      for i, c in result.nn:
        if c.kind == nnkHiddenStdConv:
          let nnn = c[1].copy
          if nnn.kind == nnkBracket and i == result.nn.len-1:
            result.nn.del(i)
            for c in nnn:
              result.nn.add c
          else:
            result.nn[i] = nnn
      if result.nn.kind in CallNodes:
        if result.nn[0].kind == nnkSym:
          result.nn[0] = ident($result.nn[0].symbol)
          # if "[]" == $result.nn[0]: # We may need this.
          #   result.nn[0] = bindsym("[]", brOpen)
          # if "[]" == $result.nn[0]: # We may need this.
          #   var nnn = newNimNode(nnkBracketExpr)
          #   for i in 1..<result.nn.len:
          #     nnn.add result.nn[i]
          #   result.nn = nnn
        for i in 0..<result.nn.len:
          # echo "#### ", result.nn[i].lisprepr
          # if result.nn[i].kind in CallNodes+{nnkIfExpr}:
          # If we need more par, try the above line first, with more node kinds.
          if result.nn[i].kind in {nnkPrefix, nnkInfix, nnkCall, nnkIfExpr}:
            result.nn[i] = newPar(result.nn[i])
          # echo "#### ", result.nn[i].lisprepr
      elif result.nn.kind == nnkHiddenDeref:
        result.nn = result.nn[0]
      elif result.nn.kind == nnkConv and result.nn[0].kind == nnkSym:
        var nnn = newCall(ident($result.nn[0].symbol))
        for i in 1..<result.nn.len:
          nnn.add result.nn[i]
        result.nn = nnn
    # echo "       repr : ", result.rep
    # echo "       node : ", result.nn.lisprepr
  result = go(n,i,j).nn
  # echo result.treerepr
  # echo "<<<< convert"
template staticint(x): expr =
  intVal if x.kind == nnkSym: x.symbol.getImpl else: x
macro unrollfor(i: untyped, lo, hi: int, n: untyped): stmt =
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

####################
# seqset
type
  seqset[T] = object
    s: seq[T]
proc len(s: seqset): auto = s.s.len
iterator items[T](s: seqset[T]): T =
  for i in s.s:
    yield i
iterator pairs[T](s: seqset[T]): (int, T) =
  for i, j in s.s:
    yield (i, j)
proc contains[T](s: seqset[T], x: T): bool =
  for i in s:
    if x == i:
      return true
  return false
proc init[T](s: var seqset[T]) = newseq(s.s,0)
proc incl[T](s: var seqset[T], x: T) =
  if not (x in s):
    s.s.add(x)
proc incl[T](s: var seqset[T], x: seqset[T]) =
  for i in x:
    s.incl(i)
proc `+`[T](x: seqset[T], y: seqset[T]): seqset[T] =
  result = x
  result.incl(y)
proc `+=`[T](x: var seqset[T], y: seqset[T]) =
  x.incl(y)
proc excl[T](s: var seqset[T], x: T) =
  for n, i in s.s:
    if x == i:
      s.s.del(n)
      break
proc excl[T](s: var seqset[T], x: seqset[T]) =
  for i in x:
    s.excl i
proc `-`[T](x: seqset[T], y: seqset[T]): seqset[T] =
  result = x
  result.excl(y)
proc intersection[T](x: seqset[T], y:seqset[T]): seqset[T] =
  result.init
  for i in x:
    if i in y:
      result.incl(i)

####################
# index type
type
  gTindex[id,lo,hi:static[int]] = object {.requiresInit.}
    # `i` auto inits to 0, which is bad
    # `requiresInit` in v0.13 gives warning without an explicit initialization
    i: range[lo..hi]
converter idx2int*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): int = i.i
converter idx2float*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): float = i.i.float
iterator items*[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): t =
  var i = t(i: lo)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
proc `$`[id,lo,hi:static[int]](x: gTindex[id,lo,hi]): string =
  $x.i & ":Idx[" & $id & "," & $lo & "," & $hi & "]"
var IndexID {.compileTime.} = 0
proc nextIndexID: int {.compileTime.} =
  result = IndexID
  inc IndexID
template IndexType*(lo, hi: int): expr =
  type Index = gTindex[nextIndexID(),lo,hi]
  Index
template staticInbound(n, lo, hi: static[int]): expr =
  static:
    if n < lo or n > hi:
      error "index out of bounds: " & $n
proc index*[id,lo,hi:static[int]](t:typedesc[gTindex[id,lo,hi]], n:static[int]): t {.inline.} =
  n.staticInbound lo, hi
  t(i: n)
template index*[id,lo,hi:static[int]](n:int, t:typedesc[gTindex[id,lo,hi]]): expr =
  index(t, n)
proc `index=`*[id,lo,hi:static[int]](ix:var gTindex[id,lo,hi], n:static[int]) {.inline.} =
  n.staticInbound lo, hi
  ix.i = n

####################
# tensor types
type
  gT1[V;id1,lo1,hi1:static[int]] = object
    data: array[lo1..hi1,V]
  gT2[V;id1,lo1,hi1,id2,lo2,hi2:static[int]] = object
    data: array[lo2..hi2,array[lo1..hi1,V]]
template Tensor*(t: typedesc, i1: typedesc): expr =
  type Tensor = genTensorType(t, i1.id, i1.lo, i1.hi)
  Tensor
template Tensor*(t: typedesc, i1: typedesc, i2: typedesc): expr =
  type Tensor = genTensorType(t, i1.id, i1.lo, i1.hi, i2.id, i2.lo, i2.hi)
  Tensor
macro genTensorType(t: typed, ix: varargs[int]): expr =
  # echo "\n>>>> genTensorType"
  let n = ix.len div 3
  case n
  of 1: result = newNimNode(nnkBracketExpr).add(bindsym"gT1", t)
  of 2: result = newNimNode(nnkBracketExpr).add(bindsym"gT2", t)
  else: error "unimplemented"
  for i in ix:
    result.add i
  # debug result
  # echo "<<<< genTensorType"

# indexing
proc `[]`*[V;id1,lo1,hi1:static[int]](x: gT1[V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1]): V {.inline.} =
  x.data[i1.i]
proc `[]`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1]): var V {.inline.} =
  x.data[i1.i]
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V {.inline.} =
  x.data[i2.i][i1.i]
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): var V {.inline.} =
  x.data[i2.i][i1.i]
proc `[]=`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1], y: V) {.inline.} =
  x.data[i1.i] = y
proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) {.inline.} =
  x.data[i2.i][i1.i] = y

####################
# dummy index type
type
  gTindexDummy[id,lo,hi:static[int]] = object
converter dummy2int*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): int {.nodecl.} = discard
converter dummy2float*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): float {.nodecl.} = discard

template Dummy*[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): expr =
  type Dummy = gTindexDummy[id,lo,hi]
  Dummy
template IndexType[id,lo,hi:static[int]](t: typedesc[gTindexDummy[id,lo,hi]]): expr =
  type Index = gTindex[id,lo,hi]
  Index
template IndexType[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): expr =
  t.type.IndexType
iterator items*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  type Index = IndexType(t)
  var i = Index(i: lo)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
template head*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  IndexType(t)(i: lo)
iterator tail*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  type Index = IndexType(t)
  const lo1 = lo + 1
  if lo1 <= hi:
    var i = Index(i: lo1)
    while true:
      yield i
      if i.i == hi: break
      inc i.i
proc tail*(t: gTindexDummy): type(t) {.nodecl.} = discard
macro choice(n: int, v: varargs[expr]): expr =
  let i = n.staticint.int
  if i >= 1 and i <= v.len:
    result = v[i-1]
  else:
    error "Index number, " & $i & ", out of range [1," & $v.len & "]"
template IndexType*[V;id1,lo1,hi1:static[int]](t: gT1[V,id1,lo1,hi1], n: int): expr =
  type
    Index1 = gTindex[id1,lo1,hi1]
  choice(n, Index1)
template IndexType*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](t: gT2[V,id1,lo1,hi1,id2,lo2,hi2], n: int): expr =
  type
    Index1 = gTindex[id1,lo1,hi1]
    Index2 = gTindex[id2,lo2,hi2]
  choice(n, Index1, Index2)
template index*[id,lo,hi:static[int]](d:gTindexDummy[id,lo,hi], n:static[int]): expr =
  index(IndexType(d), n)

proc `[]`*[V;id1,lo1,hi1:static[int]](x: gT1[V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1]): V {.nodecl.} = discard
proc `[]`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1]): var V {.nodecl.} = discard
proc `[]=`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1], y: V) {.nodecl.} = discard

proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V {.nodecl.} = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V {.nodecl.} = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V {.nodecl.} = discard

proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): var V {.nodecl.} = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): var V {.nodecl.} = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): var V {.nodecl.} = discard

proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) {.nodecl.} = discard
proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) {.nodecl.} = discard
proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) {.nodecl.} = discard

####################
# tensor ops
template staticfor[id,lo,hi:static[int]](i: untyped, t: typedesc[gTindex[id,lo,hi]], n: untyped): expr =
  unrollfor j, lo, hi:
    staticforbody(i, j, t, n)
template staticfor[id,lo,hi:static[int]](i: untyped, t: typedesc[gTindexDummy[id,lo,hi]], n: untyped): expr =
  type Index = gTindex[id,lo,hi]
  staticfor(i,Index,n)
template staticfor[id,lo,hi:static[int]](i: untyped, d: gTindexDummy[id,lo,hi], n: untyped): expr =
  staticfor(i,d.type,n)
macro staticforbody(i: untyped, j: int, t: untyped, n: untyped): untyped =
  # echo "\n>>>> staticfor"
  let
    ix = newCall(bindsym"index", t, j)
  result = replace(n, i, ix)
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< staticfor"
macro staticforstmt(n: typed): untyped =
  # echo "\n>>>> staticforstmt"
  # echo n.treerepr
  expectKind(n, nnkForStmt)
  expectKind(n[1], CallNodes)
  assert "items" == $n[1][0].symbol
  let
    t = n[1][1]
    i = n[0]
    id = gensym(nskForVar, "__" & $i.symbol)
    ii = newCall(bindsym"index", t, id)
    s = convert(n[2], i, ii)
  result = quote do:
    unrollfor `id`, `t`.lo, `t`.hi:
      `s`
  # echo result.treerepr
  # echo "<<<< staticforstmt"
type
  dummyTree = object
    idx: seqset[NimNode]
    branch: seq[dummyTree]
proc treerepr(t: dummyTree): string {.compileTime.} =
  proc `$`(s: seqset[NimNode]): string =
    result = "["
    for i in s:
      result &= $i & ","
    if ',' == result[^1]: result[^1] = ']'
    else: result &= "]"
  proc go(t: dummyTree, pre: string): string =
    result = pre & $t.idx & "\n"
    if t.branch.len > 0:
      for i in t.branch:
        result &= go(i, pre & "  ")
  return go(t, "")
proc genDummyTree(n: NimNode): dummyTree =
  # echo "\n>>>> genDummyTree"
  # echo n.lisprepr
  proc isDummyType(n: NimNode): bool =
    # echo "## isDummyType got: ", n.lisprepr
    let t =
      if n.kind == nnkSym: n.gettype
      elif n.kind in CallNodes and n[0].kind == nnkSym: n[0].gettype[1]
      else: newEmptyNode()
    # if n.kind in CallNodes and n[0].kind == nnkSym: echo "call type: ", n[0].gettype.lisprepr
    # if n.kind in CallNodes and n[0].kind == nnkClosedSymChoice:
    #   echo "  ### ", n[0].gettype.lisprepr
    #   for c in n[0]:
    #     echo "  ## ", c.lisprepr, " : ", c.gettype[1].lisprepr
    #     echo "  -> ", c.gettype[1].sametype gTindexDummy.gettype
    #     var s = newCall(c)
    #     for i in 1..<n.len:
    #       s.add n[i]
    #     echo s.gettype.lisprepr
    # echo "## dummy type check got type: ", t.repr
    result = t.sametype gTindexDummy.gettype
    # echo "isDummyType returns: ", result
  proc skipDummyCheck(n: NimNode, i: int): bool =
    # result = n.kind notin CallNodes + {
    #   nnkStmtList, nnkBlockStmt, nnkBracket,
    #   nnkIfStmt, nnkWhenStmt, nnkCaseStmt, nnkWhileStmt, nnkTryStmt,
    #   nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv
    # }
    result = n.kind in {nnkConstSection, nnkVarSection, nnkLetSection}
    result = result or n.kind == nnkForStmt and i < 2 # We check only the body.
    if result:
      echo "skipDummyCheck ", i, " ", n.lisprepr
      echo "    => ", result
  result.idx.init
  newseq result.branch, n.len
  if n.isDummyType:
    result.idx.incl n
  else:
    for i, c in n:
      let t = if n.skipDummyCheck i: newEmptyNode().genDummyTree else: c.genDummyTree
      result.idx += t.idx
      result.branch[i] = t
  # echo "<<<< genDummytree"
proc isVarArg(n: NimNode): bool =
  n.kind == nnkBracketExpr and $n[0].symbol == "var"
proc localDummyAt(ds: seq[dummyTree], i: int): seqset[NimNode] =
  result = ds[i].idx
  for n in 0..<ds.len:
    if n != i:
      result.excl ds[n].idx
const autoSumFunctions = ["=", "+=", "-=", "*=", "/=", "[]="]
const autoSumFunctionNoBracket = ["=", "+=", "-=", "*=", "/="]
const autoSumOps = ["+", "-", "*", "/"]
proc dummyStr(n: NimNode): string =
  let s = n.repr.strip
  var id = newString(s.len)
  var j = 0
  for i in 0..<s.len:
    if s[i] in IdentChars:
      id[j] = s[i]
      inc j
    elif id[j] != '_':
      id[j] = '_'
      inc j
  if j != s.len: id.setLen j
  return id
proc dummyLoopGen(ix: seqset[NimNode], n: NimNode): NimNode =
  proc reCall(n: NimNode): NimNode =
    # Look up symbol again to change a proc call to an iterator call.
    # FIXME: needs a more sophisticated treatment.
    if n.kind in CallNodes:
      result = n.copy
      result[0] = ident($n[0])
    else:
      result = n
  result = n.copy
  for i in ix:
    # echo i.repr, " : ", i.gettype.lisprepr
    # var ii = i.copy
    # if ii.kind in CallNodes: ii[0] = ident($ii[0])
    let
      id = gensym(nskForVar, "__" & i.dummyStr)
      ii = i.reCall
      body = result.convert(i, id)
    result = newNimNode(nnkForStmt).add(id, ii, body)
proc getlhs(n: NimNode): NimNode =
  # echo "getlhs: ", n.treerepr
  if n.kind == nnkAsgn:
    result = n[0]
  elif n.kind in CallNodes and $n[0] in autoSumFunctionNoBracket:
    result = n[1]
  elif n.kind in CallNodes and $n[0] == "[]=":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len-1:
      result.add n[i]
  else:
    error "Failed to get the LHS of NimNode:\n" & n.treerepr
proc getlhsix(s: seq[dummyTree]): seqset[NimNode] =
  result.init
  for i in 0..<s.len-1: # Every but last belongs to the left hand side.
    result.incl s[i].idx
proc needAutoSum(n: NimNode, t: dummyTree): bool =
  let rhsLocalIx = t.idx - t.branch.getlhsix
  result = n.kind == nnkAsgn or (n.kind in CallNodes and $n[0].symbol in autoSumFunctions) and
    rhsLocalIx.len > 0
macro splitLhsDuplicate(n: typed): typed =
  echo "\n>>>> splitLhsDuplicate <= ", n.repr
  # x[a,b] = y[b]
  #  -> x[a.head,b] = y[b]
  #     x[a.tail,b] = x[a.head,b]
  # echo ">>>> splitLhsduplicate: ", n.lisprepr
  # echo "     ", n.repr
  result = n                    # By default.
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhsIx = t.branch[^1].idx
      lhsLocalIx = t.idx - rhsIx
    # echo "lhs:        ", lhs.lisprepr
    # echo "lhsLocalIx: ", lhsLocalIx.repr
    if lhsLocalIx.len > 0:
      var
        stmtHead = n
        constHead = newNimNode(nnkConstSection)
        lhsTail = newseq[NimNode](lhsLocalIx.len)
      for m in 0..<lhsTail.len:
        lhsTail[m] = lhs
      for n, i in lhsLocalIx:
        let
          iheadCall = newCall(bindsym"head", i)
          ihead = gensym(nskConst, "__C__" & i.dummyStr)
          itail = newCall(bindsym"tail", i)
        constHead.add(newNimNode(nnkConstDef).add(ihead, newEmptyNode(), iheadCall))
        stmtHead = stmtHead.convert(i, ihead)
        for m in 0..<lhsTail.len:
          if m < n:
            lhsTail[m] = lhsTail[m].convert(i, ihead)
          elif m == n:
            lhsTail[m] = lhsTail[m].convert(i, itail)
          # Else, for m > n, do nothing.
      result = newStmtList().add(constHead, stmtHead)
      for c in lhsTail:
        result.add c.newAssignment stmtHead.getlhs
  echo "<<<< splitLhsDuplicate => ", result.repr
macro splitRhsSum(n: typed): typed =
  echo "\n>>>> splitRhsSum <= ", n.repr
  # echo "\n>>>> splitRhsSum <= ", n.treerepr
  # x[a] = y[a] `op` z[a,b]
  #  -> x[a] = z[a,b]
  #     x[a] = y[a] `op` x[a]
  # x[a,b] = y[a,c] `op` z[b,d]
  #  -> x[a,b] = y[a,c]
  #     x[a,b] `op`= z[b,d]
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      fun = $n[0]
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhs = n[^1]
      rhsT = t.branch[^1]
      rhsIx = rhsT.idx
      lhsLocalIx = t.idx - rhsIx
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
              result.add lhs.newAssignment rhs[1]
              result.add lhs.newAssignment lhs.prefix "-"
            elif fun == "+=":
              result = n.copy
              result[0] = bindsym"-="
            elif fun == "-=":
              result = n.copy
              result[0] = bindsym"+="
            elif fun in ["*=", "/="]:
              result = n.copy
              result[^1] = rhs[1]
              result = newStmtList().add(result, lhs.newAssignment lhs.prefix "-")
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
          error "not implemented for lopLocalIx.len > 0"
        elif ropLocalIx.len > 0: # Similar to lopLocalIx.len > 0, but we honor order for "*" and "/".
          error "not implemented for ropLocalIx.len > 0"
        else:                   # No local index for both operands
          result = n
      else:
        error "AutoSum only supports unary or binary ops.  Received: " & n.repr
    else:               # RHS is not a call to one of autoSumOps.
      result = n
  else:
    result = n
  echo "<<<< splitRhsSum => ", result.repr
proc accumulateAutoSum(n: NimNode): NimNode =
  echo "\n>>>> accumulateAutoSum <= ", n.repr
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      fun = $n[0]
      lhs = n.getlhs
      rhs = n[^1]
      lhsIx = t.branch.getlhsix
      rhsLocalIx = t.idx - lhsIx
    if n.kind == nnkAsgn or fun == "[]=":
      var
        stmtHead = n
        constHead = newNimNode(nnkConstSection)
        accum = newseq[NimNode](rhsLocalIx.len)
      for m in 0..<accum.len:
        accum[m] = infix(lhs, "+=", rhs)
      for n, i in rhsLocalIx:
        let
          iheadCall = newCall(bindsym"head", i)
          ihead = gensym(nskConst, "__C__" & i.dummyStr)
          itail = newCall(bindsym"tail", i)
        constHead.add(newNimNode(nnkConstDef).add(ihead, newEmptyNode(), iheadCall))
        stmtHead = stmtHead.convert(i, ihead)
        for m in 0..<accum.len:
          if m < n:
            accum[m] = accum[m].convert(i, ihead)
          elif m == n:
            accum[m] = accum[m].convert(i, itail)
          # Else, for m > n, do nothing.
      result = newStmtList().add(constHead, stmtHead)
      for c in accum:
        result.add c
    elif fun in ["*=", "/="]: # Need a temporary.
      error "not implemented for *= or /="
    else:                     # += or -= need no special treatment.
      result = n
  else:
    result = n
  echo "<<<< accumulateAutoSum => ", result.repr
macro splitMultiOp(n: typed): typed =
  echo "\n>>>> splitMultiOp <= ", n.repr
  result = n
  echo "<<<< splitMultiOp => ", result.repr
template fixpointcall(m, n: expr): expr =
  fixpoint(0, m, n, m(n))
macro fixpoint(i: static[int], m, oldn, n: typed): typed =
  # Call m repeatedly on n until nothing changes, with each step
  # type checked.  Requires m is typed -> typed.
  echo "\nfixpoint:", m.repr, ":", i, " -----> ", n.repr
  if oldn == n:
    return n
  else:
    return newCall(bindsym"fixpoint", newLit(i+1), m, n, newCall(m, n))
macro splittingHelper(n: typed): typed =
  const splits = @[bindsym"splitLhsDuplicate", bindsym"splitRhsSum", bindsym"splitMultiOp"]
  proc g(n: NimNode): NimNode =
    # echo "\n## splittingHelper:g <= ", n.treerepr
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockStmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    else:
      result = n
      for t in splits:
        result = newCall(t, result)
    # echo "## splittingHelper:g => ", result.treerepr
  result = n.g
template splitting(n: expr): expr =
  fixpointcall(splittingHelper, n)
macro autoSum(n: typed): typed =
  echo "\n>>>> autoSum <= ", n.repr
  proc g(n: NimNode): NimNode =
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    else:
      result = n.accumulateAutoSum
  result = n.g
  echo "<<<< autoSum => ", result.repr
macro looping(n: typed): typed =
  echo "\n>>>> looping: <= ", n.repr
  proc g(n: NimNode): NimNode =
    echo "\n>>>> looping:g <= ", n.repr
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    else:
      let
        t = n.genDummyTree
        lhsIx = t.branch.getlhsix
        rhsLocalIx = t.idx - lhsIx
        otherIx = t.idx - rhsLocalIx
      # echo t.treerepr
      result = rhsLocalIx.dummyLoopGen otherIx.dummyLoopGen n
    echo "<<<< looping:g => ", result.repr
  result = n.g
  echo "<<<< looping => ", result.repr
macro fusionHelper(n: typed): typed =
  echo "\n>>>> fusion <= ", n.repr
  proc g(n: NimNode): NimNode =
    echo "#### fusion:g <= ", n.repr
    if n.kind == nnkStmtList:
      result = newStmtList()
      var i = 0
      while i < n.len:
        let
          fst = n[i]
          snd = if i < n.len-1: n[i+1] else: newEmptyNode()
        if fst.kind == nnkForStmt and snd.kind == nnkForStmt and
           fst.len == snd.len and fst[^2] == snd[^2]: # ^2 is loop range.
          var forstmt = newNimNode(nnkForStmt)
          for j in 0..<fst.len-1:
            forstmt.add fst[j]
          var sndBody = snd[^1]
          for j in 0..<snd.len-2: # All loop variables.
            sndBody = sndBody.replace(snd[j], fst[j])
          forstmt.add newStmtList().add(fst[^1], sndBody)
          result.add forstmt
          inc i, 2
        else:
          result.add fst.g
          inc i
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind == nnkForStmt and n[^1].kind == nnkStmtList:
      result = newNimNode(nnkForStmt)
      for j in 0..<n.len-1:
        result.add n[j]
      result.add n[^1].g
    else:
      result = n
    echo "<<<< fusion:g => ", result.repr
  result = n.g
  echo "<<<< fusion => ", result.repr
template fusion(n: expr): expr =
  fixpointcall(fusionHelper, n)
macro tensorOps*(n: typed): typed =
  # echo "\n>>>> tensorOps"
  # echo "tensorOps received: ", n.repr
  const transforms = @[bindsym"splitting", bindsym"autoSum", bindsym"looping", bindsym"fusion"]
  result = n
  for t in transforms:
    result = newCall(t, result)
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< tensorOps"

proc `$`*(v: gT1): string =
  # We don't need to put explicit generic params.
  # Using `IndexType(T,N)` we can get the type.
  # Thus we can avoid exporting implementation details,
  # and users can write generic code for their tensors.
  tensorOps:
    var i: Dummy(IndexType(v, 1))
    result = ""
    if i == i.type.lo:
      result = "["
    else:
      result &= "\t"
    result &= $v[i]
    if i < i.type.hi:
      result &= ","
    else:
      result &= "\t]"
proc `$`*(m: gT2): string =
  tensorOps:                    # Does not work if put in proc pragma.
    var
      i: Dummy(IndexType(m, 1))
      j: Dummy(IndexType(m, 2))
      # k: Dummy(IndexType(m, 0)) # compile time error: out of bounds
    result = ""
    if i == i.type.lo:
      if j == j.type.lo:
        result &= "[[ "
      else:
        result &= "\n [ "
    else:
      result &= "\t"
    result &= $m[i,j]
    if i < i.type.hi:
      result &= ","
    else:
      result &= "\t]"
      if j == j.type.hi:
        result &= "]"

when isMainModule:
  type
    Spin = IndexType(1,4)
    Color = IndexType(1,4)
  block:
    echo "\n* test index types"
    assert(not(Spin is Color), "Spin shouldn't be the same as Color")
    var
      s: Spin
      # The following 3 are syntactically equivalent
      # ss = 5.index(Spin)            # compile time error: out of bounds
      c = Color.index 2
      # c2 = index(Color,0)           # compile time error: out of bounds
    echo c
    c.index = 1
    echo c
    echo s, "  initialized to 0, which is bad, how can we check?"
    # s = Color.index(3)          # compile time error: wrong type
    # s = Spin.index(9)           # compile time error: out of bounds
    const
      one = 1
      two = 2
    s = Spin.index(two * one)
    echo s

  block:
    echo "\n* test static and non static loops"
    var
      v, sv: Tensor(float, Spin)
    echo "\n  * staticfor"
    # staticfor i, Color:         # compile time error: type mismatch
    #   sv[i] = i * 0.1 + 1.0
    staticfor i, Spin:
      sv[i] = i * 0.1 + 1.0
      echo "  [", i, "]: ", sv[i]
    echo "\n  * staticforstmt"
    staticforstmt:
      for i in Spin:
        v[i] += i * 10.0 - 10.0
        v[i] += 100.0
        echo "  [", i, "]: ", v[i]+`*`(2.0,sv[i])
        echo "  [", i, "]: ", v[i]+2.0*sv[i]
    echo "\n  * non static, but safe"
    for i in Spin:
      echo "  [", i, "]: ", sv[i]

  block:
    echo "\n* test arithmatic with indices"
    type
      s2 = IndexType(3, 4)
      c3 = IndexType(0, 2)
    var
      scv: Tensor(float, s2, c3)
    for j in c3:
      for i in s2:
        scv[i,j] = float i*10+j
        echo "[", i, ",", j, "]: ", scv[i,j]

  block:
    var
      a, b: Dummy(Spin)
      x, y: Tensor(float, Spin)
      m: Tensor(float, Spin, Spin)
      mn: float
    echo "\n* test dummy"
    echo "\n  * test staticfor dummy"
    mn = 0
    staticfor i, a:
      m[i, Spin.index(2)] = (i-1.0)*0.1
      echo "  m[",i,",2] = ",m[i,Spin.index(2)]
      mn += m[i,i]
      echo "  mn = ", mn
    echo "\n  * test staticforstmt dummy"
    block:
      staticforstmt:
        for i in a:             # Dummy works as loop range
          m[i, Spin.index(1)] = (i-1.0)*1.0
          echo "  m[",i,",1] = ",m[i,Spin.index(1)]
    echo "\n  * test for dummy"
    block:
      for i in a:               # Dummy works as loop range
        m[i, Spin.index(1)] = m[i, Spin.index(1)] + 100.0
        echo "  m[",i,",1] = ",m[i,Spin.index(1)]
    echo "\n  * test auto loop dummy"
    tensorOps:
      m[a, b] = (a-1.0)*10.0/float(10^b)
      echo "  m =\n", m
      x[a] = if a == 1: 1.0 elif a == 2: 1e-2 elif a == 3: 1e-4 else: 1e-6
      # x[a] = 1.0*a
      # echo x[a]
      echo "  x = ", x
    echo "\n  * test auto sum"
    var
      c, d: a.type
      X, I: Tensor(float, Spin, Spin)
    tensorOps:
      I[a,a] = 1.0
      echo "  I =\n", I
    tensorOps:
      mn = 0
      mn += I[a,b]*I[b,a]
      echo "  I_ab I_ba = ", mn
      X[a,b] = I[a,c]*m[c,b]
      echo "  X_ab = I_ac m_cb =\n", X
      mn = I[a,b]*m[b,a]
      echo "  I_ab m_ba = ", mn
      y[b] = m[a,b]
      echo "  y_b = m_ab = ", y
      x[a] = m[a,b]*y[b]
      echo "  x_a = m_ab y_b = ", x
      mn = m[a,b] * m[a,b]
      echo "  m.norm2 = ", mn
      X[a,b] = m[a,c]*I[c,a]
      echo "  X_ab = m_ac I_ca =\n", X
      X[a,b] = m[c,d]
      echo "  X_ab = m_cd =\n", X
    when false:
      x[a] = 1.0 + m[a,b]*y[b]
      echo "  x_a = m_ab y_b = ", x
      # X[a,b] = I[b,c]*x[c]*(m[c,d]*y[d])
      # echo "  X =\n", X
      # y[a] = m[a,b] * x[b] + x[a]
      # echo "  y = ", y

when false:
  block:
    echo "\n* test nested"
    type
      inT = IndexType(0,3)
      In = Tensor(float, inT)
      Color = IndexType(0,2)
      cm = Tensor(In, Color, Color)
    var
      i: inT.Dummy
      mu, nu: Color.Dummy
      m: cm
    tensorOps:
      m[mu,nu][i] = 1.0*i*nu
    echo m
