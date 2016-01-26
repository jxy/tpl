import macros

macro debug(n: NimNode): stmt =
  let ns = n.repr
  return quote do:
    echo `ns`, " -> \n", `n`.treerepr

type
  gTindex[id,lo,hi:static[int]] = object
    i: int
    assigned: bool
proc `$`(x: gTindex): string =
  "gTindex[" & $gTindex.id & "," & $gTindex.lo & "," & $gTindex.hi &
    "] = (i:" & $x.i & ",assigned:" & $x.assigned & ")"
var IndexID {.compileTime.} = 0
macro Index(lo, hi: int): expr =
  echo "\n>>>> Index(lo,hi)"
  result =
    newNimNode(nnkBracketExpr).add(bindSym"gTindex",IndexID.newIntLitNode,lo,hi)
  inc IndexID
  debug result
  echo "<<<< Index(lo,hi)"
macro assignIndex(n, lo, hi: int, t: typedesc): expr =
  if n.intVal < lo.intVal or n.intVal > hi.intVal:
    error "index out of bounds: " & $n.intVal
  return quote do:
    `t`(i: `n`, assigned: true)
template Index(t:typedesc, n:int): expr =
  assignIndex(n, t.lo, t.hi, t)
template Index(n:int, t:typedesc): expr =
  assignIndex(n, t.lo, t.hi, t)
type
  Spin = Index(1,4)
  Color = Index(1,4)
assert(not(Spin is Color), "Spin shouldn't be the same as Color")
var
  s: Spin    # unassigned for dummy index
  # ss = 5.Index(Spin)            # compile time error: out of bounds
  c = 3.Index(Color)
  # c2 = Index(0,Color)           # compile time error: out of bounds
echo c
echo s
# s = Color.Index(3)              # compile time error: wrong type
s = Spin.Index(3)
echo s
