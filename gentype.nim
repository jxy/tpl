import macros

macro debug(n: NimNode): stmt =
  let ns = n.repr
  return quote do:
    echo `ns`, " -> \n", `n`.treerepr

type
  gTindex[id,lo,hi:static[int]] = object
    i: int
proc `$`(x: gTindex): string =
  "gTindex[" & $gTindex.id & "," & $gTindex.lo & "," & $gTindex.hi & "] = " & $x.i
var IndexID {.compileTime.} = 0
macro Index(lo, hi: int): expr =
  echo "\n>>>> Index(lo,hi)"
  result =
    newNimNode(nnkBracketExpr).add(
      bindSym"gTindex",IndexID.newIntLitNode,lo,hi)
  inc IndexID
  debug result
  echo "<<<< Index(lo,hi)"
macro assignIndex(n, lo, hi: int, t: typedesc): expr =
  echo n.lisprepr
  if n.intVal < lo.intVal or n.intVal > hi.intVal:
    error "index out of bounds: " & $n.intVal
  return quote do:
    `t`(i: `n`)
template Index(t:typedesc, n:int): expr =
  assignIndex(n, t.lo, t.hi, t)
template Index(n:int, t:typedesc): expr =
  assignIndex(n, t.lo, t.hi, t)
type
  Spin = Index(1,4)
  Color = Index(1,4)
assert(not(Spin is Color), "Spin shouldn't be the same as Color")
var
  s: Spin
  # ss = 5.Index(Spin)            # compile time error: out of bounds
  c = 3.Index(Color)
  # c2 = Index(0,Color)           # compile time error: out of bounds
echo c
echo s
# s = Color.Index(3)              # compile time error: wrong type
const
  one = 1
  two = 2
s = Spin.Index(two * one)
echo s

type
  gT1[V;id1:static[int];I1] = object
    data: array[I1,V]
  gT2[V;id1,id2:static[int];I1;I2] = object
    data: array[I2,array[I1,V]]
template Tensor(t: typedesc, i1: typedesc): expr =
  genTensorType(t, i1.id, i1.lo, i1.hi)
template Tensor(t: typedesc, i1: typedesc, i2: typedesc): expr =
  genTensorType(t, i1.id, i1.lo, i1.hi, i2.id, i2.lo, i2.hi)
macro genTensorType(t: typed, ix: varargs[int]): expr =
  echo "\n>>>> genTensorType"
  let n = ix.len div 3
  case n
  of 1: result = newNimNode(nnkBracketExpr).add(ident"gT1", t)
  of 2: result = newNimNode(nnkBracketExpr).add(ident"gT2", t)
  else: error "unimplemented"
  for i in 0..<n:
    result.add(ix[3*i])
  for i in 0..<n:
    result.add(
      newNimNode(nnkBracketExpr).add(
        bindsym"range", infix(ix[3*i+1],"..",ix[3*i+2])))
  echo result.repr
  echo "<<<< genTensorType"
proc `[]`[V;id1:static[int],I1,lo1,hi1](x: gT1[V,id1,I1], i1: gTindex[id1,lo1,hi1]): V =
  x.data[i1.i]
proc `[]`[V;id1,id2:static[int],I1,lo1,hi1,I2,lo2,hi2](x: gT2[V,id1,id2,I1,I2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V =
  x.data[i2.i][i1.i]
var
  sv: Tensor(float, Spin)
echo sv[1.Index(Spin)]
#   cv: gT1[float,Color.id,Color.lo..Color.hi]
# type
#   SV = gT1[float,Spin.id,Spin.lo..Spin.hi]
  # SCV = gT[SV,Color.id,Color.lo,Color.hi]
  # SCV = Tensor(float, Spin, Color)
var
  # scv: gT[gT[float,0,1,4],1,1,4]
  scv: Tensor(float, Spin, Color)
  sm: Tensor(float, Spin, Spin)
echo scv[1.Index(Spin),2.Index(Color)]
echo sm[1.Index(Spin),2.Index(Spin)]
