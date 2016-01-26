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
  result = quote do:
    gTindex[`IndexID`,`lo`,`hi`]
    # newNimNode(nnkDistinctTy).add(
    #   newNimNode(nnkBracketExpr).add(
    #     bindSym"gTindex",lo,hi,st))
  inc IndexID
  debug result
  echo "<<<< Index(lo,hi)"
macro assignIndex(n, lo, hi: int, t: typedesc): expr =
  if n.intVal < lo.intVal or n.intVal > hi.intVal:
    error "index out of bounds: " & $n.intVal
  return quote do:
    `t`(i: `n`, assigned: true)
template Index(n:int, t:typedesc): expr =
  assignIndex(n, t.lo, t.hi, t)
type
  Spin = Index(1,4)
  Color = Index(1,4)
assert(not(Spin is Color))
var
  s: Spin    # unassigned for dummy index
  # ss = 5.Index(Spin)            # compile time error
  c = 3.Index(Color)
  # c2 = Index(5,Color)           # compile time error
echo s
echo c
#[
import macros

type
  G[a,b:static[int]] = distinct int
  GG = distinct G[1,2]
  g[a,b:static[int]] = int
  gg = distinct g[1,2]
type
  f[a,b:static[int]] = object
    init: bool
    idx: int
    # case init: bool
    # of true: idx: int
    # else: stub: void
  ff {.borrow: `.`.} = distinct f[1,2]

# converter toff(x:int): ff = ff(init: true, idx: x)

# proc idx(x:ff): int = idx(f[1,2](x))
var
  vgd = 1.GG
  vgg = 2.gg
  vf = f[1,2](init: true, idx: 3)
  vff = vf.ff

echo vgd.int
echo vgg.int
echo vf.idx
echo vff.idx
]#
