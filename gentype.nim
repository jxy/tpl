import macros

template debug(x: expr): expr =
  template arg: expr = x
  let s = getast(arg())[0]
  echo "* ", s.repr, " -> \n  ", x.lisprepr

proc replace(n: NimNode, i: NimNode, j: NimNode): NimNode =
  if n == i: return j
  result = n.copyNimNode
  for c in n:
    if c == i: result.add j
    else: result.add c.replace(i, j)
macro unrollfor(i: untyped, lo, hi: int, n: untyped): stmt =
  result = newNimNode(nnkStmtList)
  template staticint(x): expr =
    intVal if x.kind == nnkSym: x.symbol.getImpl else: x
  let
    ll = staticint lo
    hh = staticint hi
  for j in ll..hh:
    result.add(n.replace(i, newIntLitNode(j)))

####################
# index type
type
  gTindex[id,lo,hi:static[int]] = object {.requiresInit.}
    # `i` auto inits to 0, which is bad
    # `requiresInit` in v0.13 gives warning without an explicit initialization
    i: range[lo..hi]
proc `$`(x: gTindex): string =
  "indexType[" &
    $gTindex.id & "," &
    $gTindex.lo & "," &
    $gTindex.hi &
    "] = " & $x.i
var IndexID {.compileTime.} = 0
macro index(lo, hi: int): expr =
  echo "\n>>>> index(lo,hi)"
  result = newNimNode(nnkBracketExpr).add(
    bindSym"gTindex", IndexID.newIntLitNode, lo, hi)
  inc IndexID
  debug result
  echo "<<<< index(lo,hi)"
template staticInbound(n, lo, hi: int) =
  static:
    if n < lo or n > hi:
      error "index out of bounds: " & $n
template index(t:typedesc, n:int): expr =
  n.staticInbound t.lo, t.hi
  t(i: n)
template index(n:int, t:typedesc): expr =
  index(t, n)
proc `index=`(ix:var gTindex, n:static[int]) {.inline.} =
  n.staticInbound gTindex.lo, gTindex.hi
  ix.i = n

####################
# tensor types
type
  gT1[V;id1,l1:static[int]] = object
    data: array[0..l1-1,V]
  gT2[V;id1,l1,id2,l2:static[int]] = object
    data: array[0..l1*l2-1,V]
template Tensor(t: typedesc, i1: typedesc): expr =
  genTensorType(t, i1.id, 1-i1.lo+i1.hi)
template Tensor(t: typedesc, i1: typedesc, i2: typedesc): expr =
  genTensorType(t, i1.id, 1-i1.lo+i1.hi, i2.id, 1-i2.lo+i2.hi)
macro genTensorType(t: typed, ix: varargs[int]): expr =
  echo "\n>>>> genTensorType"
  let n = ix.len div 2
  case n
  of 1: result = newNimNode(nnkBracketExpr).add(bindsym"gT1", t)
  of 2: result = newNimNode(nnkBracketExpr).add(bindsym"gT2", t)
  else: error "unimplemented"
  for i in ix:
    result.add i
  debug result
  echo "<<<< genTensorType"
template `[]`[V;id1,l1,lo1,hi1:static[int]](x: gT1[V,id1,l1], i1: gTindex[id1,lo1,hi1]): V =
  let i = i1.i-lo1
  x.data[i]
template `[]`[V;id1,l1,id2,l2,lo1,hi1,lo2,hi2:static[int]](x: gT2[V,id1,l1,id2,l2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V =
  let i = (i2.i-lo2)*l1+i1.i-lo1
  x.data[i]
template `[]=`[V;id1,l1,lo1,hi1:static[int]](x: var gT1[V,id1,l1], i1: gTindex[id1,lo1,hi1], y: V) =
  let i = i1.i-lo1
  x.data[i] = y
template `[]=`[V;id1,l1,id2,l2,lo1,hi1,lo2,hi2:static[int]](x: var gT2[V,id1,l1,id2,l2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) =
  let i = (i2.i-lo2)*l1+i1.i-lo1
  x.data[i] = y

####################
# dummy index type
type
  gTindexDummy[id,lo,hi:static[int]] = object
template dummy[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): expr =
  gTindexDummy[id,lo,hi]
proc `[]`[V;id1,l1,lo1,hi1:static[int]](x: gT1[V,id1,l1], i1: gTindexDummy[id1,lo1,hi1]): V = discard
proc `[]`[V;id1,l1,id2,l2,lo1,hi1,lo2,hi2:static[int]](x: gT2[V,id1,l1,id2,l2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V = discard
proc `[]=`[V;id1,l1,lo1,hi1:static[int]](x: var gT1[V,id1,l1], i1: gTindexDummy[id1,lo1,hi1], y: V) = discard
proc `[]=`[V;id1,l1,id2,l2,lo1,hi1,lo2,hi2:static[int]](x: var gT2[V,id1,l1,id2,l2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) = discard

####################
# tensor ops
macro tensorOps(n: typed): typed =
  echo "\n>>>> tensorOps"
  echo n.treerepr
  echo "<<<< tensorOps"

when isMainModule:
  type
    Spin = index(1,4)
    Color = index(1,4)
  block:
    assert(not(Spin is Color), "Spin shouldn't be the same as Color")
    var
      s: Spin
      # ss = 5.index(Spin)            # compile time error: out of bounds
      c = Color.index 2
      # c2 = index(0,Color)           # compile time error: out of bounds
    echo c
    c.index = 1
    echo c
    echo s, "  initialized to 0, which is bad, how can we check?"
    # s = Color.index(3)              # compile time error: wrong type
    const
      one = 1
      two = 2
    s = Spin.index(two * one)
    echo s

  block:
    var
      sv: Tensor(float, Spin)
    unrollfor i, 1, 4:
      echo "[", i, "]: ", sv[Spin.index i]

  block:
    type
      s2 = index(3, 4)
      c3 = index(0, 2)
    var
      scv: Tensor(float, s2, c3)
    unrollfor j, 0, 2:
      unrollfor i, 3, 4:
        scv[s2.index i, c3.index j] = float i*10+j
        echo "[", i, ",", j, "]: ", scv[s2.index i, c3.index j]

  block:
    var
      a, b: dummy(Spin)
    tensorOps:
      var
        x, y: Tensor(float, Spin)
        m: Tensor(float, Spin, Spin)
      y[a] = m[a,b] * x[b] + x[a]
