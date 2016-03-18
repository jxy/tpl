import unittest
import tpl

type
  S = IndexType(0,1)
  C = IndexType(0,2)
  SV = Tensor(float, [S])
  SM = Tensor(float, [S,S])
  CV = Tensor(float, [C])
  CM = Tensor(float, [C,C])
  SCV = Tensor(float, [S,C])
  CSV = Tensor(float, [C,S])
var
  x, y: float
  sv, sv2, sv3: SV
  sm: SM
  cv: CV
  cm: CM
  scv: SCV
  csv: CSV
  i, j: S.Dummy
  a, b: C.Dummy
prepareDummy(S, C)
tensorOps:
  sv[i] = 1.0+i
  cv[a] = 0.1*(1.0+a)
  cm[a,b] = a+0.1*b
  sm[i,j] = i+0.1*j
  echo "sv = ", sv
  echo "cv = ", cv
  echo "cm =\n", cm
  echo "sm =\n", sm
  sv2 = sm * sv + sv
  echo "sv2 = sm * sv + sv = ", sv2
  sv3 = sm * sv
  sv3 += sv
  check(sv3[i] == sv2[i])
  csv = sm * sv + sv
  echo "csv = sm * sv + sv =\n", csv
  check(csv[i] == sv2[i])
  sv2 = sv + sv * sm
  echo "sv2 = sv + sv * sm = ", sv2
  sv3 = sv * sm
  sv3 += sv
  check(sv2[i] == sv3[i])
  sv2 = 0
  sv2 += sv + sv * sm
  echo "sv2 = 0; sv2 += sv + sv * sm = ", sv2
  check(sv2[i] == sv3[i])
  sv2 = sv * sm + sv * sm
  sv3 = 2.0 * sv * sm
  echo "sv2 = sv * sm + sv * sm = ", sv2
  echo "sv3 = 2.0 * sv * sm = ", sv3
  check(sv2[i] == sv3[i])
  x = sv*sm*sv
  echo "x = sv*sm*sv = ", x
  sv2 = sv*sm
  y = sv2*sv
  check(x == y)
  sv = sv*sm
  echo "sv = sv*sm = ", sv
  check(sv[i] == sv2[i])
