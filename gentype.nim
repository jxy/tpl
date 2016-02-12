import macros
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
      result = (true, j)
    else:
      result.rep = false
      result.nn = n.copyNimNode
      for c in n:
        let cc = c.go(i,j)
        result.nn.add cc.nn
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
          if "[]" == $result.nn[0]:
            var nnn = newNimNode(nnkBracketExpr)
            for i in 1..<result.nn.len:
              nnn.add result.nn[i]
            result.nn = nnn
        for i in 0..<result.nn.len:
          # if result.nn[i].kind in CallNodes+{nnkIfExpr}:
          # If we need more par, try the above line first, with more node kinds.
          if result.nn[i].kind in {nnkPrefix, nnkInfix, nnkCall, nnkIfExpr}:
            result.nn[i] = newPar(result.nn[i])
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
template index*(n:static[int], t:typedesc): expr =
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
template IndexType[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): expr =
  type Index = gTindex[id,lo,hi]
  Index
iterator items*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  type Index = IndexType(t)
  var i = Index(i: lo)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
template head*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): expr =
  index(IndexType(t), lo)
iterator tail*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  type Index = IndexType(t)
  var i = Index(i: lo+1)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
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
  result.idx.init
  newseq result.branch, n.len
  if n.kind == nnkSym:
    let t = n.gettype
    # echo n.repr, "  <of>  ", t.treerepr
    if t.kind == nnkSym and "gTindexDummy" == $t.symbol:
      result.idx.incl n
  else:
    for i, c in n:
      let t = c.genDummyTree
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
const autoSumFunctionNames = ["=", "+=", "-=", "[]="]
const autoSumFunctionNamesAsgn = ["=", "[]="]
proc requireAutoSum(n: NimNode, dt: dummyTree): bool =
  proc isAsgnCall(n: NimNode): bool =
    if n.kind in CallNodes:
      let
        f = n[0].gettype      # the function type
        fname = $n[0].symbol  # the function name
        firstArg = f[2]
      var restArgHasVar = false
      for i in 3..<f.len:
        if f[i].isVarArg:
          restArgHasVar = true
          break
      return fname in autoSumFunctionNames and
        firstArg.isVarArg and not restArgHasVar
    else:
      return false
  let lastLocalDummy = localDummyAt(dt.branch, dt.branch.len-1)
  return (n.kind == nnkAsgn or n.isAsgnCall) and lastLocalDummy.len > 0
proc dummyLoopGen(n: NimNode, ix: seqset[NimNode]): NimNode =
  result = n.copy
  for i in ix:
    # echo i.repr, " : ", i.gettype.lisprepr
    let
      id = gensym(nskForVar, "__" & $i.symbol)
      body = result.convert(i, id)
    result = newNimNode(nnkForStmt).add(id, i, body)
proc accumLoopGen(accumIx: seqset[NimNode], asgn: NimNode, accum: NimNode): NimNode =
  var
    asgnLoop = asgn
    accumLoops = newseq[NimNode](accumIx.len)
  for n in 0..<accumLoops.len:
    accumLoops[n] = accum
  for n, i in accumIx:
    let
      ihead = newCall(ident"head", i)
      id = gensym(nskForVar, "__" & $i.symbol)
    asgnLoop = asgnLoop.convert(i, ihead)
    for m in 0..<accumLoops.len:
      if m > n:
        accumLoops[m] = newNimNode(nnkForStmt).add(id, i, accumLoops[m].convert(i, id))
      elif m == n:
        accumLoops[m] = newNimNode(nnkForStmt).add(id, newCall(ident"tail", i), accumLoops[m].convert(i, id))
      else:
        accumLoops[m] = accumLoops[m].convert(i, ihead)
  result = newStmtList().add asgnLoop
  for n in accumLoops:
    result.add(n)
proc autoSum(n: NimNode, dt: dummyTree): NimNode =
  # echo "\n>>>> autoSum"
  # echo n.treerepr
  # echo n.repr
  proc getlhsix(s: seq[dummyTree]): seqset[NimNode] =
    result.init
    for i in 0..<s.len-1: # Every but last belongs to the left hand side.
      result.incl s[i].idx
  let
    rhs = n[^1]              # Last child is the right hand side.
    rhsDT = dt.branch[^1]
    rhsIx = rhsDT.idx
    lhsIx = getlhsix(dt.branch)
    rhsLocalIx = dt.idx - lhsIx
    lhsLocalIx = dt.idx - rhsIx
    sharedIx = lhsIx - lhsLocalIx
    sharedIxLoop = n.dummyLoopGen sharedIx
  if rhs.kind in CallNodes:
    for i in 1..<rhs.len:
      let localIx = localDummyAt(rhsDT.branch, i) - sharedIx
      if localIx.len > 0:
        error "subExpr autoSum not implemented"
  if n.kind == nnkAsgn or $n[0].symbol in autoSumFunctionNamesAsgn:
    var accum: NimNode
    if n.kind == nnkAsgn:
      accum = infix(n[0], "+=", n[1])
    elif $n[0].symbol == "[]=":
      var bracket = newNimNode(nnkBracketExpr)
      for i in 1..<n.len-1:
        bracket.add n[i]
      accum = infix(bracket, "+=", n[^1])
    result = accumLoopGen(rhsLocalIx, sharedIxLoop, accum.dummyLoopGen(sharedIx))
  else:
    result = sharedIxLoop.dummyLoopGen(rhsLocalIx)
  # echo "autoSum generated tree:\n" & result.treerepr
  hint "autoSum generated code:\n" & result.repr
  if lhsLocalIx.len > 0:
    error "lhsLocalIx autoSum not implemented"
  # echo "<<<< autoSum"
proc dummyLoop(n: NimNode): NimNode =
  # echo "\n>>>> dummyLoop"
  # echo n.treerepr
  let
    dt = genDummyTree(n)
  # echo dt.treerepr
  if dt.idx.len > 0:
    if n.requireAutoSum dt:
      result = n.autoSum dt
    else:
      result = n.dummyLoopGen dt.idx
  else:
    result = n
  # echo result.treerepr
  # echo "<<<< dummyLoop"

macro tensorOps*(n: typed): typed =
  # echo "\n>>>> tensorOps"
  result = newStmtList()
  if n.kind == nnkStmtList:
    for s in n:
      result.add s.dummyLoop
  else:
    result.add n.dummyLoop
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< tensorOps"

proc `$`*(v: gT1): string =
  # We don't need to put explicit generic params.
  # Using `IndexType(T,N)` we can get the type.
  # Thus we can avoid exporting implementation details,
  # and users can write generic code for their tensors.
  var
    i: Dummy(IndexType(v, 1))
    s = ""
  tensorOps:
    block:
      if i == i.type.lo:
        s = "["
      else:
        s &= "\t"
      s &= $v[i]
      if i < i.type.hi:
        s &= ","
      else:
        s &= "\t]"
  return s
proc `$`*(m: gT2): string =
  var
    i: Dummy(IndexType(m, 1))
    j: Dummy(IndexType(m, 2))
    # k: Dummy(IndexType(m, 0)) # compile time error: out of bounds
    s = ""
  tensorOps:
    block:
      if i == i.type.lo:
        if j == j.type.lo:
          s &= "[[ "
        else:
          s &= "\n [ "
      else:
        s &= "\t"
      s &= $m[i,j]
      if i < i.type.hi:
        s &= ","
      else:
        s &= "\t]"
        if j == j.type.hi:
          s &= "]"
  return s

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
      # X[a,b] = m[a,c]*I[c,a]
      # echo "  X_ab = m_ac I_ca =\n", X
      # X[a,b] = I[b,c]*x[c]*(m[c,d]*y[d])
      # echo "  X =\n", X
      # y[a] = m[a,b] * x[b] + x[a]
      # echo "  y = ", y
      # y[a] += 1.0 + x[b] * m[b,a]
      # echo "  y = ", y

#[
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
]#
