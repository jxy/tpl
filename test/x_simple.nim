import TPL

tpl:
  S = IndexType(4)
  C = IndexType(3)
  type
    SV = Tensor([S], float)
    CV = Tensor([C], float)
    CM = Tensor([C,C], float)
    CSV = Tensor([C,S], float)
    SCM = Tensor([S,C,C], float)
  var
    x: float
    sv: SV
    cv: CV
    cm: CM
    csv: CSV
    scm: SCM
    i = S.dummy
    a = C.dummy
  # 0.588=sv+.×cv+.×⍤1(scm←(csv←(sv←⍳4)∘.×cv)∘.×cv)+.×⍤2 1cv←0.1×⍳3
  sv[i] = 1.0+i
  cv[a] = 0.1*(1.0+a)
  csv = sv*cv
  scm = csv*cv
  x = sv*cv*scm*cv
  cm = scm[S.index 2]
  echo "scm[",2,"] =\n",cm
  echo "sv = ",sv
  echo "cv = ",cv
  echo "csv = ",csv
  echo "x = sv*cv*scm*cv = ", x
