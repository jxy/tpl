import TPL
tplSilent:
  S = IndexType(0,3)
  C = IndexType(0,2)
var
  m: array[0..3, int]
  i = S.dummy
  a = C.dummy
  v: Tensor([S], int, ptr[type(m)])
v.data = addr m
tpl:
  v[i] = 10*i
  echo v
