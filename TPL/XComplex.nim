# Experimental complex index support
import macros
import tensorTypes,indexTypes

const
  TPL_complex* = -1
type
  Complex* = gTindexUninitialized[TPL_complex, 0, 1]
# Complex multiplication is defined as:
# x_a = TPLComplexCoeff_abc y_b z_c
const
  TPL_Complex_Coeff = [
    [[1.0, 0.0], [0.0, -1.0]],
    [[0.0, 1.0], [1.0,  0.0]]
  ]
proc complexCoefficient(a, b, c: int): float {.inline.} =
  TPL_Complex_Coeff[a][b][c]
proc complexCoeff*(a, b, c: NimNode): NimNode =
  result = newCall(bindsym"complexCoefficient",
                   newCall(bindsym"indexValue", a),
                   newCall(bindsym"indexValue", b),
                   newCall(bindsym"indexValue", c))
# type
#   gP2I1[D,V;n1,ci1,id1,lo1,hi1:static[int]] = object
#     data*: ptr[D]
# template `[]`*[D,V;id1,lo1,hi1,ci1:static[int]](t: gP2I1[D,V,1,ci1,id1,lo1,hi1], i1: int): expr =
#   t.data[][ci1,i1]
# template `[]=`*[D,V;id1,lo1,hi1,ci1:static[int]](t: gP2I1[D,V,1,ci1,id1,lo1,hi1], i1: int, y: V): expr =
#   t.data[][ci1,i1] = y
# template `[]`*[D,V;id1,lo1,hi1,ci1:static[int]](t: gP2I1[D,V,2,ci1,id1,lo1,hi1], i1: int): expr =
#   t.data[][i1,ci1]
# template `[]=`*[D,V;id1,lo1,hi1,ci1:static[int]](t: gP2I1[D,V,2,ci1,id1,lo1,hi1], i1: int, y: V): expr =
#   t.data[][i1,ci1] = y
template partIndexTensor[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](nix: int, x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], ix: int): expr =
  const
    cid1 = id2
    clo1 = lo2
    chi1 = hi2
    cix = ix
    cni = nix
  type
    # DD = D
    VV = V
    T = object
  when cni == 1:
    template `[]`(t: T, i1: int): expr = x.data[cix, i1]
    template `[]=`(t: T, i1: int, y: VV): expr = x.data[cix, i1] = y
  else:
    when cni == 2:
      template `[]`(t: T, i1: int): expr = x.data[i1, cix]
      template `[]=`(t: T, i1: int, y: VV): expr = x.data[i1, cix] = y
    else:
      error "nix = " & $nix & ", not in [1,2]"
  #   P = gP2I1[DD,VV,cni,cix,cid1,clo1,chi1]
  # gT1[P,VV,cid1,clo1,chi1](data: P(data: addr(x.data)))
  var t: T
  gT1[T,VV,cid1,clo1,chi1](data: t)
template re*[D,V](x: gT1[D,V,TPL_complex,0,1]): expr =
  x.data[0]
template im*[D,V](x: gT1[D,V,TPL_complex,0,1]): expr =
  x.data[1]
template re*[D,V;id2,lo2,hi2:static[int]](x: gT2[D,V,TPL_complex,0,1,id2,lo2,hi2]): expr =
  partIndexTensor(1, x, 0)
template im*[D,V;id2,lo2,hi2:static[int]](x: gT2[D,V,TPL_complex,0,1,id2,lo2,hi2]): expr =
  partIndexTensor(1, x, 1)
