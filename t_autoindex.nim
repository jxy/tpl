import tpl

type
  S = IndexType(0,1)
  C = IndexType(0,1)
  SV = Tensor(float, [S])
  SM = Tensor(float, [S,S])
  CV = Tensor(float, [C])
  CM = Tensor(float, [C,C])
  SCV = Tensor(float, [S,C])
  CSV = Tensor(float, [C,S])
# prepareAutoIndex(SV, SM, CV, CM, SCV, CSV)
var
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
  scv[i] = sv[i]+i
  echo "scv[i] = sv[i]+i =\n", scv
  sv[i] = scv[i]
  echo "sv[i] = scv[i] = ", sv
  scv[i] += sv[i]
  echo "scv[i] += sv[i] =\n", scv
  sm[i,i] = i+1.0
  echo "sm =\n", sm
  csv[j] = -scv[i]*sm[i,j]
  echo "csv[j] = -scv[i]*sm[i,j] =\n", csv
tensorOpsTrace TPLDebug.output:
  scv[i] += (i+0.5)*csv[i]
tensorOps:
  echo "scv[i] += (i+0.5)*csv[i] =\n", scv
  # sv2 = sv
  # echo "naive asssignment: sv2 = sv = ", sv2
  # sv = 2.0
  # sv2 = 2.0*sv
  # echo "sv2 = 2.0*sv = ", sv2
