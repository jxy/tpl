import unittest
import strutils
import TPL

colorOutput = false

const
  nc = 3
  ns = 4
# custom data type
type D = seq[int]
# with chatty indexing operation
proc `[]`(x: D, c, s: int): int =
  echo "[]() ", x.repr.strip, "[", c, ",", s, "]"
  x[c+s*nc]
proc `[]`(x: var D, c, s: int): var int =
  echo "[]var() ", x.repr.strip, "[", c, ",", s, "]"
  x[c+s*nc]
proc `[]=`(x: var D, c, s: int, y: int) =
  echo "[]=() ", x.repr.strip, "[", c, ",", s, "] = ", y
  x[c+s*nc] = y


tplSilent:
  C = IndexType(0,nc-1)
  S = IndexType(0,ns-1)
type
  T = Tensor([C, S], int, D)    # Tensor([Index], element, container)
var
  a = C.dummy
  i = S.dummy
  d: T
newseq(d.data, nc*ns)           # direct .data access
test "Custom data layout":
  tpl:
    d[a,i] = 10*a+i
    check(d.data == @[0, 10, 20, 1, 11, 21, 2, 12, 22, 3, 13, 23])
    echo d
    d[a,i] += 1000*i+100*a
    check(d.data == @[0, 110, 220, 1001, 1111, 1221, 2002, 2112, 2222, 3003, 3113, 3223])
    echo d
