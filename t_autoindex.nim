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
const
  u = UniversalDummyIndex
prepareDummy(S, C)
tensorOps:
  sv[u] = sv[u]
  sv[u] += sv[u]
  sv[u] = scv[u,u]*cv[u]
  sv[u] += scv[u,u]*cv[u]
  sm[u,u] = sv[u]*sv[u]
  sv[u] = sv[u]
  sm[u,u] = sm[u,u]
  # sm[u,u] = scv[u,u]*sm[u,u]
  # sm[u,u] = scv[u,u]*cm[u,u]*sm[u,u]
  # sm[u,u] = scv[u,u]*cm[u,u]*cm[u,u]*sm[u,u]
  # scv[u,u] = scv[u,u]*cm[u,u]*cm[u,u]*sm[u,u]
  sv[i] = 0.1*i
  echo "sv = ", sv
  sv2 = sv
  echo "naive asssignment: sv2 = sv = ", sv2
  # sv = 2.0
  # sv2 = 2.0*sv
  # echo "sv2 = 2.0*sv = ", sv2
