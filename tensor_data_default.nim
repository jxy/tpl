type
  D1*[V;lo1,hi1:static[int]] = object
    data: array[lo1..hi1,V]
  D2*[V;lo1,hi1,lo2,hi2:static[int]] = object
    data: array[lo2..hi2,array[lo1..hi1,V]]

proc `[]`*[V;lo1,hi1:static[int]](x: D1[V,lo1,hi1], i1: int): V {.inline.} =
  x.data[i1]
proc `[]`*[V;lo1,hi1:static[int]](x: var D1[V,lo1,hi1], i1: int): var V {.inline.} =
  x.data[i1]
proc `[]`*[V;lo1,hi1,lo2,hi2:static[int]](x: D2[V,lo1,hi1,lo2,hi2], i1: int, i2: int): V {.inline.} =
  x.data[i2][i1]
proc `[]`*[V;lo1,hi1,lo2,hi2:static[int]](x: var D2[V,lo1,hi1,lo2,hi2], i1: int, i2: int): var V {.inline.} =
  x.data[i2][i1]
proc `[]=`*[V;lo1,hi1:static[int]](x: var D1[V,lo1,hi1], i1: int, y: V) {.inline.} =
  x.data[i1] = y
proc `[]=`*[V;lo1,hi1,lo2,hi2:static[int]](x: var D2[V,lo1,hi1,lo2,hi2], i1: int, i2: int, y: V) {.inline.} =
  x.data[i2][i1] = y
