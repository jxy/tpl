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
# prepareAutoIndex(SV, SM, CV, CM, SCV, CSV)
var
  x: float
  sv, sv2: SV
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
  echo "sv = ", sv
  cv[a] = 0.1*(1.0+a)
  echo "cv = ", cv
  scv[i] = sv[i]+i
  echo "scv[i] = sv[i]+i =\n", scv
  scv += cv
  echo "scv += cv =\n", scv
  scv -= 0.5*sv
  echo "scv -= 0.5*sv =\n", scv
  x = scv
  echo "x = scv = ", x
  cm[a,b] = a+0.1*b
  echo "cm =\n", cm
  cm = scv
  echo "cm = scv =                # NOTE: Off-diag terms remain.\n", cm
  sv = scv
  echo "sv = scv = ", sv
  sm[i,j] = i+0.1*j
  echo "sm =\n", sm
  csv = -scv*sm
  echo "csv = -scv*sm =\n", csv
  # sv2 = sv + sv * sv
  # echo "sv2 = sv + sv * sv = ", sv2
  # sv2 = sm + sv * sv
  # echo "sv2 = sm + sv * sv = ", sv2
  scv[i] += (if 0 == (i and 1): (i-0.5)*csv[i] else: (i+0.5)*csv[i])
  echo "scv[i] += (if 0 == (i and 1): (i-0.5)*csv[i] else: (i+0.5)*csv[i]) =\n", scv
  x = sv*sv
  echo "x = sv*sv = ", x
  x = sm*sm
  echo "x = sm*sm = ", x
  sv2 = 0.5*sv
  echo "sv2 = 0.5*sv = ", sv2
  sv2 += sv * sm
  echo "sv2 += sv*sm = ", sv2
  cv = scv * sv
  echo "cv = scv*sv = ", cv
  # x = sv*sm*sv
  # echo "x = sv*sm*sv = ", x
  sv2 = sv
  echo "naive asssignment: sv2 = sv = ", sv2
  sv = 2.0*sv
  echo "sv = 2.0*sv = ", sv
