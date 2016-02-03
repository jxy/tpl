import macros

iterator pairs(n: NimNode): tuple[key: int, val: NimNode] =
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
  echo "\n>>>> convert"
  echo n.treerepr
  echo i.treerepr
  echo j.treerepr
  proc go(n: NimNode, i: NimNode, j: NimNode): tuple[rep: bool, nn: NimNode] =
    echo "  ==== go : ", n.lisprepr
    if n == i:
      result = (true, j)
    else:
      result.rep = false
      result.nn = n.copyNimNode
      for c in n:
        echo "   {{       ", c.kind
        let cc = c.go(i,j)
        echo "   }}"
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
      if result.nn.kind in CallNodes and result.nn[0].kind == nnkSym:
        result.nn[0] = ident($result.nn[0].symbol)
        if "[]" == $result.nn[0]:
          var nnn = newNimNode(nnkBracketExpr)
          for i in 1..<result.nn.len:
            nnn.add result.nn[i]
          result.nn = nnn
        for i in 0..<result.nn.len:
          # if result.nn[i].kind in CallNodes:
          # If we need more par, try the above line first.
          if result.nn[i].kind in {nnkInfix, nnkCall}:
            result.nn[i] = newPar(result.nn[i])
      elif result.nn.kind == nnkHiddenDeref:
        result.nn = result.nn[0]
      elif result.nn.kind == nnkConv and result.nn[0].kind == nnkSym:
        var nnn = newCall(ident($result.nn[0].symbol))
        for i in 1..<result.nn.len:
          nnn.add result.nn[i]
        result.nn = nnn
    echo "       repr : ", result.rep
    echo "       node : ", result.nn.lisprepr
  result = go(n,i,j).nn
  echo result.treerepr
  echo "<<<< convert"
macro unrollfor(i: untyped, lo, hi: int, n: untyped): stmt =
  echo "\n>>>> unrollfor"
  echo n.treerepr
  result = newNimNode(nnkStmtList)
  template staticint(x): expr =
    intVal if x.kind == nnkSym: x.symbol.getImpl else: x
  let
    ll = staticint lo
    hh = staticint hi
  for j in ll..hh:
    result.add(n.replace(i, newLit(j)))
  echo result.treerepr
  echo result.repr
  echo "<<<< unrollfor"

####################
# seqset
type
  seqset[T] = object
    s: seq[T]
proc len(s: seqset): auto = s.s.len
iterator items[T](s: seqset[T]): T =
  for i in s.s:
    yield i
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
  yield i
  while i.i < hi:
    inc i.i
    yield i
proc `$`[id,lo,hi:static[int]](x: gTindex[id,lo,hi]): string =
  "gTindex[" & $id & "," & $lo & "," & $hi & "] = " & $x.i
var IndexID {.compileTime.} = 0
proc nextIndexID: int {.compileTime.} =
  result = IndexID
  inc IndexID
template IndexType*(lo, hi: int): expr =
  gTindex[nextIndexID(),lo,hi]
proc staticInbound(n, lo, hi: static[int]) {.inline.} =
  static:
    if n < lo or n > hi:
      error "index out of bounds: " & $n
proc index*[id,lo,hi:static[int]](t:typedesc[gTindex[id,lo,hi]], n:static[int]): t {.inline.} =
  n.staticInbound lo, hi
  t(i: n)
proc index*(n:static[int], t:typedesc): t {.inline.} =
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
  genTensorType(t, i1.id, i1.lo, i1.hi)
template Tensor*(t: typedesc, i1: typedesc, i2: typedesc): expr =
  genTensorType(t, i1.id, i1.lo, i1.hi, i2.id, i2.lo, i2.hi)
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
proc `[]=`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1], y: V) {.inline.} =
  x.data[i1.i] = y
proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) {.inline.} =
  x.data[i2.i][i1.i] = y

####################
# dummy index type
type
  gTindexDummy[id,lo,hi:static[int]] = object

proc `+`*(x: gTindexDummy, y: int): int = discard
proc `-`*(x: gTindexDummy, y: int): int = discard

template Dummy*[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): expr =
  gTindexDummy[id,lo,hi]
template IndexType*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): expr =
  gTindex[id,lo,hi]

proc `[]`*[V;id1,lo1,hi1:static[int]](x: gT1[V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1]): V = discard
proc `[]`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1]): var V = discard
proc `[]=`*[V;id1,lo1,hi1:static[int]](x: var gT1[V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1], y: V) = discard

proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V = discard

proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): var V = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): var V = discard
proc `[]`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): var V = discard

proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) = discard
proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) = discard
proc `[]=`*[V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) = discard

####################
# tensor ops
template staticfor[id,lo,hi:static[int]](i: untyped, t: typedesc[gTindex[id,lo,hi]], n: untyped): expr =
  unrollfor j, lo, hi:
    staticforbody(i, j, t, n)
template staticfor[id,lo,hi:static[int]](i: untyped, t: typedesc[gTindexDummy[id,lo,hi]], n: untyped): expr =
  type T = gTindex[id,lo,hi]
  staticfor(i,T,n)
macro staticforbody(i: untyped, j: int, t: untyped, n: untyped): untyped =
  echo "\n>>>> staticfor"
  let
    ix = newCall(bindsym"index", t, j)
  result = replace(n, i, ix)
  echo result.treerepr
  echo result.repr
  echo "<<<< staticfor"
macro staticforstmt(n: typed): untyped =
  # echo "\n>>>> staticforstmt"
  # echo n.treerepr
  expectKind(n, nnkForStmt)
  expectKind(n[1], CallNodes)
  assert "items" == $n[1][0].symbol
  let
    t = n[1][1]
    i = n[0]
    id = ident("__" & $i.symbol)
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
  proc go(t: dummyTree, pre: string): string =
    var idx = "["
    for i in t.idx:
      idx &= " " & $i & ","
    if ',' == idx[^1]: idx[^1] = ' '
    idx &= "]"
    result = pre & idx & "\n"
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
proc dummyLoopCall(n: NimNode): NimNode =
  echo "\n>>>> dummyLoopCall"
  expectKind(n, nnkCallKinds)
  echo n.treerepr
  let
    fun = n[0].gettype
    fid = ident($n[0].symbol)
  echo '"', fid, "\" -> ", fun.lisprepr
  if "proc" != $fun[0].symbol:
    warning "calling " & n[0].repr & " not supported"
  echo n[1].lisprepr, " -> ", n[1].gettype.lisprepr
  let
    dt = genDummyTree(n)
  echo dt.treerepr
  result = n.copy
  for i in dt.idx:
    echo i.repr, " : ", i.gettype.lisprepr
    let
      id = ident("__" & $i.symbol)
      body = result.convert(i, id)
    result = quote do:
      type T = IndexType(`i`)
      for `id` in T:
        `body`
    # result = newNimNode(nnkForStmt).add(id,ty,result.convert(i, id)) # convert SIGSEGV
    # result = newCall(!"staticfor",id,ty,result.replace(i, id))
  echo result.treerepr
  echo "<<<< dummyLoopCall"

macro tensorOps*(n: typed): typed =
  echo "\n>>>> tensorOps"
  expectKind(n, {nnkStmtList,nnkCall})
  result = newNimNode(nnkStmtList)
  if n.kind == nnkCall:
    result.add n.dummyLoopCall
  elif n.kind == nnkStmtList:
    for s in n:
      if s.kind in nnkCallKinds:
        result.add s.dummyLoopCall
      else:
        hint "skipping: " & s.lisprepr
        result.add s
  else:
    echo "unhandled NimNode: ", n.repr
  echo result.treerepr
  echo "<<<< tensorOps"

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
    staticfor i, type(a):
      m[i, Spin.index(2)] = (i-1.0)*0.1
    staticfor i, type(a):
      echo "  m[",i,",2] = ",m[i,Spin.index(2)]
      mn += m[i,i]
      echo "  mn = ", mn
    echo "\n  * test for dummy" # Not working
    # for i in type(a):
    # type T = undummy(a)
    # for i in T:
    # for i in IndexType(a):
    type T = IndexType(a)
    for i in T:
      m[i, Spin.index(1)] = (i-1.0)*1.0
      echo "  m[",i,",1] = ",m[i,Spin.index(1)]
    echo "\n  * test auto loop dummy"
    tensorOps:
      m[a, Spin.index(1)] = float(a-1)*1.0
      m[a, Spin.index(2)] = float(a-1)*0.1
      m[a, Spin.index(3)] = float(a-1)*0.01
      m[a, Spin.index(4)] = float(a-1)*0.001
      echo "  m[", a, ",", b, "] = ", m[a,b]
      # mn = m[a,b] * m[a,b]
      # echo "m.norm2 = ", mn
      # x[a] = float a - 1
      # echo "x[", a, "] = ", x[a]
      # y[a] = m[a,b] * x[b] + x[a]
      # echo "y[", a, "] = ", y[a]
      # y[a] += x[a]
      # echo "y[", a, "] = ", y[a]
