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
# index types
type
  gTindex[id,lo,hi:static[int]] = object
    i: int
proc `$`(x: gTindex): string =
  "indexType[" &
    $gTindex.id & "," &
    $gTindex.lo & "," &
    $gTindex.hi &
    "] = " & $x.i
var IndexID {.compileTime.} = 0
macro Index(lo, hi: int): expr =
  echo "\n>>>> Index(lo,hi)"
  result = newNimNode(nnkBracketExpr).add(
    bindSym"gTindex", IndexID.newIntLitNode, lo, hi)
  inc IndexID
  debug result
  echo "<<<< Index(lo,hi)"
template staticInbound(n, lo, hi: int) =
  static:
    if n < lo or n > hi:
      error "index out of bounds: " & $n
template Index(t:typedesc, n:int): expr =
  n.staticInbound t.lo, t.hi
  t(i: n)
template Index(n:int, t:typedesc): expr =
  Index(t, n)
proc `Index=`(ix:var gTindex, n:static[int]) {.inline.} =
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


when isMainModule:
  type
    Spin = Index(1,4)
    Color = Index(1,4)
  assert(not(Spin is Color), "Spin shouldn't be the same as Color")
  var
    s: Spin
    # ss = 5.Index(Spin)            # compile time error: out of bounds
    c = Color.Index 2
    # c2 = Index(0,Color)           # compile time error: out of bounds
  echo c
  c.Index = 1
  echo c
  echo s
  # s = Color.Index(3)              # compile time error: wrong type
  const
    one = 1
    two = 2
  s = Spin.Index(two * one)
  echo s

  var
    sv: Tensor(float, Spin)
  echo 1, " : ", sv[Spin.Index 1]
  echo 2, " : ", sv[Spin.Index 2]
  echo 3, " : ", sv[Spin.Index 3]
  echo 4, " : ", sv[Spin.Index 4]
  type
    s2 = Index(3, 4)
    c3 = Index(0, 2)
  var
    scv: Tensor(float, s2, c3)
  unrollfor j, 0, 2:
    unrollfor i, 3, 4:
      scv[s2.Index i, c3.Index j] = float i*10+j
      echo "[", i, ",", j, "] : ", scv[s2.Index i, c3.Index j]
