import strutils
import TPL
import tensorTypes

proc `$`*[D,V;id1,lo1,hi1:static[int]](v: gT1[D,V,id1,lo1,hi1]): string {.tplSilent.} =
  var i = IndexType(v, 0).dummy
  result = "["
  if true:                    # This would put them in the same loops.
    result &= " " & $v[i]
    if i < hi1:
      result &= ","
  result &= " ]"
proc `$`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](m: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): string {.tplSilent.} =
  type
    I1 = IndexType(m, 0)
    I2 = IndexType(m, 1)
  var
    i = I1.dummy
    j = I2.dummy
    ws: Tensor([I1], int)
    xs: Tensor([I1, I2], string)
  result = ""
  xs[i,j] = $m[i,j]
  if ws[i] < xs[i,j].len:
    ws[i] = xs[i,j].len
  if true:
    if i == lo1:
      if j == lo2:
        result &= "[["
      else:
        result &= "\n ["
    result &= " " & xs[i,j] & spaces(ws[i] - xs[i,j].len)
    if i < hi1:
      result &= ","
    else:
      result &= " ]"
      if j < hi2:
        result &= ","
      else:
        result &= "]"
