import macros
import seqset
import utils
import tensor_data_default
import strutils

type
  TPLDebug* {.pure.} = enum
    none, final, output, flow, detail
proc `$`(t: TPLDebug): string =
  case t
  of TPLDebug.none: "NONE"
  of TPLDebug.final: "FINAL"
  of TPLDebug.output: "OUTPUT"
  of TPLDebug.flow: "FLOW"
  of TPLDebug.detail: "DETAIL"
var
  TPLDebugLevel {.compileTime.} = TPLDebug.final
proc dbg(s: string = "", n: NimNode = newEmptyNode(), lvl: TPLDebug = TPLDebug.final) =
  if TPLDebugLevel >= lvl:
    let ns = if TPLDebugLevel >= TPLDebug.detail: n.treerepr else: n.repr
    if n == newEmptyNode():
      echo "DBG:", lvl, ":", s
    else:
      echo "DBG:", lvl, ":", s, ns

####################
# index type
type
  gTindex[id,lo,hi:static[int]] = object {.requiresInit.}
    # `i` auto inits to 0, which is bad
    # `requiresInit` in v0.13 gives warning without an explicit initialization
    i: range[lo..hi]
converter idx2int*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): int = i.i
converter idx2float*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): float = i.i.float
iterator indices(id, lo, hi: static[int]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
  var i = gTindex[cid,clo,chi](i: lo)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
iterator items*[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): t =
  var i = t(i: lo)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
proc `$`*[id,lo,hi:static[int]](x: gTindex[id,lo,hi]): string =
  $x.i & ":Idx[" & $id & "," & $lo & "," & $hi & "]"
var IndexID {.compileTime.} = 0
proc nextIndexID: int {.compileTime.} =
  result = IndexID
  inc IndexID
template IndexType*(lo, hi: int): typedesc = gTindex[nextIndexID(),lo,hi]
template staticInbound(n, lo, hi: static[int]): expr =
  static:
    if n < lo or n > hi:
      error "index out of bounds: " & $n
proc index*[id,lo,hi:static[int]](t:typedesc[gTindex[id,lo,hi]], n:static[int]): t {.inline.} =
  n.staticInbound lo, hi
  t(i: n)
template index*[id,lo,hi:static[int]](n:int, t:typedesc[gTindex[id,lo,hi]]): expr =
  index(t, n)
proc `index=`*[id,lo,hi:static[int]](ix:var gTindex[id,lo,hi], n:static[int]) {.inline.} =
  n.staticInbound lo, hi
  ix.i = n

####################
# tensor types
type
  gT1[D,V;id1,lo1,hi1:static[int]] = object
    data*: D
  gT2[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]] = object
    data*: D
proc addDot(d: var NimNode, i: NimNode, id: varargs[string]) =
  for s in id:
    d.add(i.newDotExpr s.ident)
template tensorType(container, element: typed): expr =
  element
template tensorType(container, element: typed, i1: typed): expr =
  const
    id1 = i1.id
    lo1 = i1.lo
    hi1 = i1.hi
  gT1[container, element, id1, lo1, hi1]
template tensorType(container, element:typed, i1, i2: typed): expr =
  const
    id1 = i1.id
    lo1 = i1.lo
    hi1 = i1.hi
    id2 = i2.id
    lo2 = i2.lo
    hi2 = i2.hi
  gT2[container, element, id1, lo1, hi1, id2, lo2, hi2]
proc genTensorType(container, element, index: NimNode): NimNode =
  result = newCall(bindsym"tensorType", container, element)
  for i in index:
    result.add i
  # echo "<<<< genTensortype => ", result.lisprepr
macro Tensor*(container, element: typed, index: openarray[typed]): expr =
  result = genTensorType(container, element, index)
macro Tensor*(element: typed, index: openarray[typed]): expr =
  var container = newCall(bindsym"TensorDataDefault", element)
  for i in index:
    container.addDot(i, "lo", "hi")
  result = genTensorType(container, element, index)
proc isTensorType(n: NimNode): bool =
  result = $n.gettype in ["gT1", "gT2"]
  # Using sametype does not work here?!
  # result = n.gettype.sametype gT1.gettype
  # result = result or n.gettype.sametype gT2.gettype
template rank(x: gT1): int = 1
template rank(x: gT2): int = 2

macro genConv(ty: typed, el: typed): untyped =
  template defConv(convName, ta, tb: untyped): stmt =
    converter convName*(x: ta): tb {.nodecl.} = discard
    converter convName*(x: tb): ta {.nodecl.} = discard
  let conv = "__CONV_" & ty.dummyStr & "__2__" & el.dummyStr
  result = getast(defConv(ident(conv), ty, el))
  # echo "<<<< genConv => ", result.repr
template prepareAutoIndex1*[D;V;id1,lo1,hi1:static[int]](t: typedesc[gT1[D,V,id1,lo1,hi1]]): stmt =
  genConv(t, V)
template prepareAutoIndex1*[D;V;id1,lo1,hi1,id2,lo2,hi2:static[int]](t: typedesc[gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]]): stmt =
  genConv(t, V)
macro prepareAutoIndex*(ts: varargs[typed]): stmt =
  result = newStmtList()
  for t in ts:
    result.add newCall(bindsym"prepareAutoIndex1", t)

# indexing
proc `[]`*[D,V;id1,lo1,hi1:static[int]](x: gT1[D,V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1]): V {.inline.} =
  x.data[i1.i]
proc `[]`*[D,V;id1,lo1,hi1:static[int]](x: var gT1[D,V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1]): var V {.inline.} =
  x.data[i1.i]
proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V {.inline.} =
  x.data[i1.i, i2.i]
proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): var V {.inline.} =
  x.data[i1.i, i2.i]
proc `[]=`*[D,V;id1,lo1,hi1:static[int]](x: var gT1[D,V,id1,lo1,hi1], i1: gTindex[id1,lo1,hi1], y: V) {.inline.} =
  x.data[i1.i] = y
proc `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) {.inline.} =
  x.data[i1.i, i2.i] = y

####################
# dummy index type
type
  gTindexDummy[id,lo,hi:static[int]] = object
converter dummy2int*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): int {.nodecl.} = discard
converter dummy2float*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): float {.nodecl.} = discard

template Dummy*[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): typedesc[gTindexDummy[id,lo,hi]] =
  gTindexDummy[id,lo,hi]
iterator items*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
  var i = gTindex[cid,clo,chi](i: clo)
  while true:
    yield i
    if i.i == chi: break
    inc i.i
template head*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): gTindex[id,lo,hi] =
  index(gTindex[id,lo,hi], lo)
iterator tail*(id, lo, hi: static[int]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
    lo1 = lo + 1
  if lo1 <= hi:
    var i = gTindex[cid,clo,chi](i: lo1)
    while true:
      yield i
      if i.i == hi: break
      inc i.i
proc tail*(t: gTindexDummy): type(t) {.nodecl.} = discard
macro choice(n: int, v: varargs[expr]): expr =
  let i = n.staticint
  if i >= 1 and i <= v.len:
    result = v[i-1]
  else:
    error "Index number, " & $i & ", out of range [1," & $v.len & "]"
template IndexType*[D,V;id1,lo1,hi1:static[int]](t: gT1[D,V,id1,lo1,hi1], n: int): expr =
  type
    Index1 = gTindex[id1,lo1,hi1]
  choice(n, Index1)
template IndexType*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](t: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], n: int): expr =
  type
    Index1 = gTindex[id1,lo1,hi1]
    Index2 = gTindex[id2,lo2,hi2]
  choice(n, Index1, Index2)
template index*[id,lo,hi:static[int]](d:gTindexDummy[id,lo,hi], n:static[int]): expr =
  index(gTindex[id,lo,hi], n)

proc `[]`*[D,V;id1,lo1,hi1:static[int]](x: gT1[D,V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1]): V {.nodecl.} = discard
proc `[]`*[D,V;id1,lo1,hi1:static[int]](x: var gT1[D,V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1]): var V {.nodecl.} = discard
proc `[]=`*[D,V;id1,lo1,hi1:static[int]](x: var gT1[D,V,id1,lo1,hi1], i1: gTindexDummy[id1,lo1,hi1], y: V) {.nodecl.} = discard

proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V {.nodecl.} = discard
proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): V {.nodecl.} = discard
proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): V {.nodecl.} = discard

proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): var V {.nodecl.} = discard
proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2]): var V {.nodecl.} = discard
proc `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2]): var V {.nodecl.} = discard

proc `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) {.nodecl.} = discard
proc `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], i2: gTindexDummy[id2,lo2,hi2], y: V) {.nodecl.} = discard
proc `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: var gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], i2: gTindex[id2,lo2,hi2], y: V) {.nodecl.} = discard

####################
# universal dummy index
type
  gTindexDummyU = object
const UniversalDummyIndex = gTindexDummyU()
macro prepareDummy*(d: varargs[typed]): stmt =
  template convDummyU(cn, t: untyped): stmt =
    converter cn*(x: gTindexDummyU): t {.nodecl.} = discard
  result = newStmtList()
  for i in d:
    let
      id = newCall(bindsym"Dummy", i)
      conv = "__CONV_DummyU__2__" & i.dummyStr
    result.add getast(convDummyU(ident(conv), i))

template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1]): expr =
  `[]`(x, i1, UniversalDummyIndex)
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i2: gTindexDummy[id2,lo2,hi2]): expr =
  `[]`(x, UniversalDummyIndex, i2)
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1]): expr =
  `[]`(x, i1, UniversalDummyIndex)
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i2: gTindex[id2,lo2,hi2]): expr =
  `[]`(x, UniversalDummyIndex, i2)

template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindexDummy[id1,lo1,hi1], y: V): expr =
  `[]=`(x, i1, UniversalDummyIndex, y)
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i2: gTindexDummy[id2,lo2,hi2], y: V): expr =
  `[]=`(x, UniversalDummyIndex, i2, y)
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: gTindex[id1,lo1,hi1], y: V): expr =
  `[]=`(x, i1, UniversalDummyIndex, y)
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i2: gTindex[id2,lo2,hi2], y: V): expr =
  `[]=`(x, UniversalDummyIndex, i2, y)

template genUnaryOp(op: untyped): stmt =
  template op*[D,V;id1,lo1,hi1:static[int]](x: gT1[D,V,id1,lo1,hi1]): expr =
    op(x[UniversalDummyIndex])
  template op*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): expr =
    op(x[UniversalDummyIndex, UniversalDummyIndex])

macro genUOp(os: varargs[untyped]): stmt =
  result = newStmtList()
  for o in os:
    result.add newCall(bindsym"genUnaryOp", o)
genUOp(`+`, `-`)

template genBinaryOp(op: untyped): stmt =
  template op*[lD,lV;lid1,llo1,lhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: lV): expr =
    op(x[UniversalDummyIndex], y)
  template op*[rD,rV;rid1,rlo1,rhi1:static[int]](x: rV, y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
    op(x, y[UniversalDummyIndex])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
    op(x[UniversalDummyIndex], y[UniversalDummyIndex])
  template op*[lD,lV;lid1,llo1,lhi1,lid2,llo2,lhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: lV): expr =
    op(x[UniversalDummyIndex,UniversalDummyIndex], y)
  template op*[rD,rV;rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: rV, y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
    op(x, y[UniversalDummyIndex,UniversalDummyIndex])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
    op(x[UniversalDummyIndex,UniversalDummyIndex], y[UniversalDummyIndex])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
    op(x[UniversalDummyIndex], y[UniversalDummyIndex,UniversalDummyIndex])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
    op(x[UniversalDummyIndex,UniversalDummyIndex], y[UniversalDummyIndex,UniversalDummyIndex])

macro genBOp(os: varargs[untyped]): stmt =
  result = newStmtList()
  for o in os:
    result.add newCall(bindsym"genBinaryOp", o)
genBOp(`+`, `-`, `*`, `/`, `+=`, `-=`, `*=`, `/=`)

template autoIndexAsgn[lD,lV;lid1,llo1,lhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: lV): expr =
  x[UniversalDummyIndex] = y
template autoIndexAsgn[rD,rV;rid1,rlo1,rhi1:static[int]](x: rV, y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
  x = y[UniversalDummyIndex]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
  x[UniversalDummyIndex] = y[UniversalDummyIndex]
template autoIndexAsgn[lD,lV;lid1,llo1,lhi1,lid2,llo2,lhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: lV): expr =
  x[UniversalDummyIndex,UniversalDummyIndex] = y
template autoIndexAsgn[rD,rV;rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: rV, y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
  x = y[UniversalDummyIndex,UniversalDummyIndex]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
  x[UniversalDummyIndex,UniversalDummyIndex] = y[UniversalDummyIndex]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
  x[UniversalDummyIndex] = y[UniversalDummyIndex,UniversalDummyIndex]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
  x[UniversalDummyIndex,UniversalDummyIndex] = y[UniversalDummyIndex,UniversalDummyIndex]
macro autoIndexAsgn[T](lhs: T, rhs: T): stmt =
  dbg "autoIndexAsgn <= lhs: ", lhs, TPLDebug.detail
  dbg "autoIndexAsgn <= rhs: ", rhs, TPLDebug.detail
  var lhs = lhs
  if lhs.kind == nnkHiddenDeref: lhs = lhs[0]
  if lhs.kind in CallNodes and $lhs[0] == "[]": # Indexing operation
    result = newNimNode(nnkBracketExpr)
    # result = newCall(ident"[]=")
    for i in 1..<lhs.len:
      result.add lhs[i]
  else:
    result = lhs
  result = newAssignment(result, rhs)
  dbg "autoIndexAsgn => ", result, TPLDebug.detail

####################
# tensor ops
macro temporaryTensorEq(lhs: untyped, rhs: typed): stmt =
  dbg "temporaryTensorEq:lhs: ", lhs, TPLDebug.detail
  dbg "temporaryTensorEq:rhs: ", rhs, TPLDebug.detail
  result = newStmtList().add(newNimNode(nnkVarSection), newAssignment(lhs, rhs))
  let rhsT = newCall(bindsym"type", rhs)
  if lhs.kind == nnkBracketExpr and lhs.len > 0:
    var tensorCall = newCall(bindsym"Tensor", rhsT, newNimNode(nnkBracket))
    for i in 1..<lhs.len:
      tensorCall[2].add newCall(bindsym"type", lhs[i])
    result[0].add newIdentDefs(lhs[0], tensorCall)
  elif lhs.kind == nnkIdent:
    result[0].add newIdentDefs(lhs, rhsT)
  else:
    error "Don't know how to create temporaryTensor from lhs: '" & lhs.repr & "' and rhs: '" & rhs.repr & "'"

macro staticforbody(i: untyped, j: int, t: untyped, n: untyped): untyped =
  # echo "\n>>>> staticfor"
  let
    ix = newCall(bindsym"index", t, j)
  result = replace(n, i, ix)
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< staticfor"
template staticfor*[id,lo,hi:static[int]](i: untyped, t: typedesc[gTindex[id,lo,hi]], n: untyped): expr =
  unrollfor j, lo, hi:
    staticforbody(i, j, t, n)
template staticfor*[id,lo,hi:static[int]](i: untyped, t: typedesc[gTindexDummy[id,lo,hi]], n: untyped): expr =
  type Index = gTindex[id,lo,hi]
  staticfor(i,Index,n)
template staticfor*[id,lo,hi:static[int]](i: untyped, d: gTindexDummy[id,lo,hi], n: untyped): expr =
  staticfor(i,d.type,n)
macro staticforstmt*(n: typed): untyped =
  # echo "\n>>>> staticforstmt"
  # echo n.treerepr
  expectKind(n, nnkForStmt)
  expectKind(n[1], CallNodes)
  assert "items" == $n[1][0].symbol
  let
    t = n[1][1]
    i = n[0]
    id = gensym(nskForVar, "__" & $i.symbol)
    ii = newCall(bindsym"index", t, id)
    s = convert(n[2], i, ii)
  result = quote do:
    unrollfor `id`, `t`.lo, `t`.hi:
      `s`
  # echo result.treerepr
  # echo "<<<< staticforstmt"
type
  dummyTree = object
    idx: seqset[NimNode]
    branch: seq[dummyTree]
proc treerepr(t: dummyTree): string {.compileTime.} =
  proc `$`(s: seqset[NimNode]): string =
    result = "["
    for i in s:
      result &= i.repr & ","
    if ',' == result[^1]: result[^1] = ']'
    else: result &= "]"
  proc go(t: dummyTree, pre: string): string =
    result = pre & $t.idx & "\n"
    if t.branch.len > 0:
      for i in t.branch:
        result &= go(i, pre & "  ")
  return go(t, "")
proc genDummyTree(n: NimNode): dummyTree =
  # echo "\n>>>> genDummyTree"
  # echo n.treerepr
  proc isDummyType(n: NimNode): bool =
    # echo "## isDummyType got: ", n.lisprepr
    let t =
      if n.kind == nnkSym: n.gettype
      elif n.kind in CallNodes and n[0].kind == nnkSym: n[0].gettype[1]
      else: newEmptyNode()
    # if n.kind in CallNodes and n[0].kind == nnkSym: echo "call type: ", n[0].gettype.lisprepr
    # echo "** dummy type check got: ", n.repr
    # echo "## dummy type check got type: ", t.repr
    result = t.sametype gTindexDummy.gettype
    # echo "isDummyType returns: ", result
  proc skipDummyCheck(n: NimNode, i: int): bool =
    # result = n.kind notin CallNodes + {
    #   nnkStmtList, nnkBlockStmt, nnkBracket,
    #   nnkIfStmt, nnkWhenStmt, nnkCaseStmt, nnkWhileStmt, nnkTryStmt,
    #   nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv
    # }
    result = n.kind in {nnkConstSection, nnkVarSection, nnkLetSection}
    result = result or n.kind == nnkForStmt and i < 2 # We check only the body.
    # if result:
    #   echo "skipDummyCheck ", i, " ", n.lisprepr
    #   echo "    => ", result
  proc g(n: NimNode): dummyTree =
    result.idx.init
    newseq result.branch, n.len
    if n.isDummyType:
      result.idx.incl n
    else:
      for i, c in n:
        let t = if n.skipDummyCheck i: newEmptyNode().g else: c.g
        result.idx += t.idx
        result.branch[i] = t
  result = n.g
  # echo "<<<< genDummytree =>\n", result.treerepr
proc isVarArg(n: NimNode): bool =
  n.kind == nnkBracketExpr and $n[0].symbol == "var"
proc localDummyAt(ds: seq[dummyTree], i: int): seqset[NimNode] =
  result = ds[i].idx
  for n in 0..<ds.len:
    if n != i:
      result.excl ds[n].idx

const autoSumFunctions = ["=", "+=", "-=", "*=", "/=", "[]="]
const autoSumFunctionNoBracket = ["=", "+=", "-=", "*=", "/="]
const autoSumOps = ["+", "-", "*", "/"]

proc getlhs(n: NimNode): NimNode =
  # echo "getlhs: ", n.treerepr
  if n.kind == nnkAsgn:
    result = if n[0].kind == nnkHiddenDeref: n[0][0] else: n[0]
  elif n.kind in CallNodes and $n[0] in autoSumFunctionNoBracket and n.len == 3:
    result = n[1]
  elif n.kind in CallNodes and $n[0] == "[]=":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len-1:
      result.add n[i]
  else:
    error "Failed to get the LHS of NimNode:\n" & n.treerepr
proc getlhsix(s: seq[dummyTree]): seqset[NimNode] =
  result.init
  for i in 0..<s.len-1: # Every but last belongs to the left hand side.
    result.incl s[i].idx
proc isAutoSumStmt(n: NimNode): bool =
  result = n.kind == nnkAsgn or (n.kind in CallNodes and $n[0] in autoSumFunctions)
proc needAutoSum(n: NimNode, t: dummyTree): bool =
  let rhsLocalIx = t.idx - t.branch.getlhsix
  result = n.isAutoSumStmt and rhsLocalIx.len > 0
proc reAssembleBinOp(n, lhs, rhs: NimNode): NimNode =
  if n.kind == nnkAsgn or
     (n.kind in CallNodes and $n[0] == "[]=" and lhs.kind == nnkBracketExpr):
    result = newAssignment(lhs, rhs)
  elif n.kind in CallNodes and n.len == 3:
    result = n.copyNimNode.add(n[0])
    for s in [lhs, rhs]:
      if s.kind == nnkPar: result.add s
      else: result.add s.newPar
  else:
    error "Don't know how to reassemble binary op for\n" &
      n.repr & "\nfrom lhs\n" & lhs.repr & "\nand rhs\n" & rhs.repr

proc rebindAssignment(n: NimNode): NimNode =
  if n.kind == nnkAsgn:
    result = newCall(bindsym"autoIndexAsgn", n[0], n[1])
  else:
    result = n
macro reAssign(n: untyped): stmt =
  dbg "reAssign <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.rebindAssignment
  result = n.g
  # dbg "reAssign => ", result, TPLDebug.flow

type
  Ixk = enum
    ixk0, ixkI, ixkE, ixkM, ixkT, ixkN
  ixtree = ref object
    case kind: Ixk
    of ixkI:
      vId, vIt: NimNode # dummy and its type
      con: bool         # if contracted
    of ixkE: vEl, vEr: ixtree  # lhs and rhs
    of ixkM: vM: seq[ixtree]   # operands of `*`
    of ixkT: vT: seq[ixtree]   # indexing of a tensor
    of ixkN: vN: seq[ixtree]   # Other NimNode
    of ixk0: discard           # Empty
proc treerepr(t: ixtree): string =
  case t.kind
  of ixk0:
    result = "--"
  of ixkI:
    result = "Ix " & t.vId.repr & ": " & t.vIt.repr & ", con: " & $t.con
  of ixkE:
    let
      lhs = t.vEl.treerepr.indent(2)
      rhs = t.vEr.treerepr.indent(2)
    result = "Eq\n" & lhs & "\n" & rhs
  of ixkM:
    result = "Mu"
    for c in t.vM:
      result &= "\n" & c.treerepr.indent(2)
  of ixkT:
    result = "Ti"
    for c in t.vT:
      result &= "\n" & c.treerepr.indent(2)
  of ixkN:
    result = "Nn"
    for c in t.vN:
      result &= "\n" & c.treerepr.indent(2)
proc `$`(t: ixtree): string = treerepr t
proc `$`(t: ptr ixtree): string = t.repr
proc contractDummyU(n: NimNode): NimNode =
  var dID {.compileTime global.} = 0
  template notEmpty(t: ixtree): bool = not t.empty
  proc empty(t: ixtree): bool =
    case t.kind
    of ixk0: result = true
    of ixkI: result = t.vId == nil
    of ixkE: result = t.vEl.empty and t.vEr.empty
    of ixkM: result = t.vM.len == 0
    of ixkT: result = t.vT.len == 0
    of ixkN: result = t.vN.len == 0
  proc add(t: var ixtree, i: ixtree) =
    if i.notempty:
      case t.kind
      of ixkM:
        t.vM.add i
      of ixkT:
        if i.kind == ixkT:
          for j in i.vT:
            t.vT.add j
        else:
          t.vT.add i
      of ixkN:
        t.vN.add i
      else:
        error "Internal error: cannot add to ixtree\n" & t.repr & "\nwith\n" & i.repr
  proc markContracted(t: var ixtree, s: NimNode) =
    case t.kind
    of ixkI:
      if t.vId == s:
        t.con = true
    of ixkE:
      t.vEl.markContracted s
      t.vEr.markContracted s
    of ixkM:
      for i in 0..<t.vM.len:
        t.vM[i].markContracted s
    of ixkN:
      for i in 0..<t.vN.len:
        t.vN[i].markContracted s
    of ixkT:
      for i in 0..<t.vT.len:
        t.vT[i].markContracted s
    of ixk0:
      discard
  proc replaceDummyU(n: NimNode): (NimNode, ixtree) =
    if n.kind == nnkHiddenCallConv and n[1] == bindsym"UniversalDummyindex":
      let
        t = n[0].symbol.getimpl[3][0] # The symbol of the return type of the converter.
        d = gensym(nskVar, "__D" & $dID & "__" & $t)
      inc dID
      result = (d, ixtree(kind: ixkI, vId: d, vIt: t))
    elif n.isAutoSumStmt:
      let
        (lhs, lt) = n.getlhs.replaceDummyU
        (rhs, rt) = n[^1].replaceDummyU
      result = (
        n.reAssembleBinOp(lhs, rhs),
        ixtree(kind: ixkE, vEl: lt, vEr: rt)
      )
    else:
      var
        nn = n.copyNimNode
        ixt =
          if n.kind in CallNodes and $n[0] == "*":
            ixtree(kind: ixkM, vM: @[])
          elif n.kind == nnkBracketExpr or (n.kind in CallNodes and $n[0] == "[]"):
            ixtree(kind: ixkT, vT: @[])
          else:
            ixtree(kind: ixkN, vN: @[])
      for c in n:
        let (r, t) = c.replaceDummyU
        nn.add r
        ixt.add t
      if ixt.empty:
        result = (n, ixtree(kind: ixk0))
      else:
        # Special rebindings here to force type check the stmt again.
        if nn.kind in CallNodes:
          if $nn[0] == "[]":
            nn[0] = bindsym"[]" # We need to index with different index types.
          # We may or may not need the following 5 lines.
          # for i in 1..<nn.len:
          #   if nn[i].kind == nnkHiddenDeref:
          #     nn[i] = nn[i][0].newPar
          #   elif nn[i].kind != nnkPar:
          #     nn[i] = nn[i].newPar
          nn = nn.newPar
        elif nn.kind == nnkHiddenDeref:
          nn = if nn[0].kind == nnkPar: nn[0] else: nn[0].newPar
        result = (nn, ixt)
  proc alltypes(t: ixtree): seqset[NimNode] =
    result.init
    case t.kind
    of ixkI:
      result.incl t.vIt
    of ixkE:
      result.incl t.vEl.alltypes
      result.incl t.vEr.alltypes
    of ixkM:
      for s in t.vM:
        result.incl s.alltypes
    of ixkT:
      for s in t.vT:
        result.incl s.alltypes
    of ixkN:
      for s in t.vN:
        result.incl s.alltypes
    of ixk0:
      discard
  proc collectDummy(t: ixtree): seq[ixtree] =
    # Collect all ixkI kinds.
    result.newseq(0)
    case t.kind
    of ixkI:
      result.add t
    of ixkE:
      result.add t.vEl.collectDummy
      result.add t.vEr.collectDummy
    of ixkM:
      for s in t.vM:
        result.add s.collectDummy
    of ixkT:
      for s in t.vT:
        result.add s.collectDummy
    of ixkN:
      for s in t.vN:
        result.add s.collectDummy
    of ixk0:
      discard
  type
    rpair = tuple
      fr: NimNode
      to: NimNode
    replacePairs = object
      data: seq[rpair]
  iterator items(s: replacePairs): rpair =
    var i = 0
    while i < s.data.len:
      yield s.data[i]
      inc i
  proc init(x: var replacePairs) =
    x.data.newseq(0)
  proc len(x: replacePairs): int =
    x.data.len
  proc add(x: var replacePairs, p: rpair) =
    var
      p = p
      changed = false
    for i in 0..<x.data.len:
      if x.data[i].fr == p.fr:
        x.data[i].to = p.to
        changed = true
      if x.data[i].to == p.fr:
        x.data[i].to = p.to
      if x.data[i].fr == p.to:
        p.to = x.data[i].to
    if not changed:
      x.data.add p
  proc add(x: var replacePairs, ps: replacePairs) =
    for p in ps.data:
      x.add p
  proc replace(n: NimNode, p: rpair): NimNode =
    n.replace(p.fr, p.to)
  proc rmReplaced(xs: seq[ixtree], ps: replacePairs): seq[ixtree] =
    result.newseq(xs.len)
    var j = 0
    for x in xs:
      assert x.kind == ixkI
      var toBeReplaced = false
      for p in ps:
        if x.vId == p.fr:
          toBeReplaced = true
          break
      if not toBeReplaced:
        result[j] = x
        inc j
    result.setlen j
  proc noncontractedIx(t: ixtree, s: NimNode): seq[NimNode] =
    result = @[]
    case t.kind
    of ixkI:
      if t.vIt == s and not t.con:
        result.add t.vId
    of ixkE:
      result.add t.vEl.noncontractedIx s
      result.add t.vEr.noncontractedIx s
    of ixkM:
      for c in t.vM:
        result.add c.noncontractedIx s
    of ixkT:
      for c in t.vT:
        result.add c.noncontractedIx s
    of ixkN:
      for c in t.vN:
        result.add c.noncontractedIx s
    of ixk0:
      discard
  proc matchDummyType(t: var ixtree, s: NimNode): replacePairs # Used in following recursions.
  proc contractMul(t: var ixtree, s: NimNode): replacePairs =
    # We contract nearby indices of tensors multiplied together.
    # hint "contractMul:t: " & t.treerepr
    # hint "contractMul:s: " & $s
    result.init
    case t.kind:
    of ixkM:
      var ixlist = newseq[seq[NimNode]](t.vM.len)
      for i in 0..<t.vM.len:
        result.add t.vM[i].contractMul s
        ixlist[i] = t.vM[i].noncontractedIx s
      for i in 1..<ixlist.len:
        if ixlist[i].len > 0:
          for prevI in countdown(i-1, 0):
            if ixlist[prevI].len > 0:
              result.add((ixlist[i][0], ixlist[prevI][^1]))
              t.vM[i].markContracted ixlist[i][0]
              ixlist[i].del 0
              t.vM[prevI].markContracted ixlist[prevI][^1]
              ixlist[prevI].del(ixlist[prevI].len-1)
              break
    of ixkT:
      for i in 0..<t.vT.len:
        result.add t.vT[i].contractMul s
    of ixkN:
      for i in 0..<t.vN.len:
        result.add t.vN[i].contractMul s
    else:
      result.init
    # hint "contractMul:t: " & t.treerepr
    # hint "contractMul:result: " & $result
  proc match2(s: NimNode, lhs, rhs: var ixtree): (replacePairs, seq[NimNode], seq[NimNode]) =
    # Try to match lhs with rhs, returns replacement pairs and
    # non-contracted indices from lhs and rhs.
    # hint "match2: " & s.repr
    # hint "match2: " & lhs.treerepr
    # hint "match2: " & rhs.treerepr
    var
      lp = lhs.matchDummyType s
      rp = rhs.matchDummyType s
      lix = lhs.noncontractedIx s
      rix = rhs.noncontractedIx s
    # hint "match2:lp: " & $lp
    # hint "match2:rp: " & $rp
    # hint "match2:lix: " & $lix
    # hint "match2:rix: " & $rix
    while lix.len != rix.len:
      if lix.len > rix.len:
        let p = lhs.contractMul s
        lix = lhs.noncontractedIx s
        if p.len == 0:
          break
        lp.add p
      else:
        let p = rhs.contractMul s
        rix = rhs.noncontractedIx s
        if p.len == 0:
          break
        rp.add p
    lp.add rp
    if lix.len == rix.len:
      for i in 0..<lix.len:
        lp.add((rix[i], lix[i]))
      result = (lp, lix, rix)
    else:
      result = (lp, lix, rix)
  proc matchDummyType(t: var ixtree, s: NimNode): replacePairs =
    # Make sure that indices of type `s` are matched.
    # hint "matchDummyType: " & s.repr
    case t.kind
    of ixkE:
      let (rp, lix, rix) = s.match2(t.vEl, t.vEr)
      # hint "matchDummyType:lix " & lix.repr
      # hint "matchDummyType:rix " & rix.repr
      # hint "matchDummyType:rp " & rp.repr
      result = rp
      if lix.len != rix.len:
        if lix.len <= 1 or rix.len <= 1: # Special Assignment Rule!
          let ix = if lix.len > 0: lix[0] else: rix[0]
          for c in lix:
            if c != ix:
              result.add((c, ix))
          for c in rix:
            if c != ix:
              result.add((c, ix))
        else:
          error "Cannot match dummy indices for type: " & s.repr
    of ixkN:
      result.init
      let n = t.vn.len - 1
      var
        changed = false
        unmatched = true
        idlen = newseq[int](n)
      while changed and unmatched:
        for i in 0..<n:
          let
            olen = idlen[i]
            (rp, lix, rix) = s.match2(t.vN[i], t.vN[i+1])
          if lix.len != rix.len:
            error "Cannot match dummy indices for type: " & s.repr
          idlen[i] = lix.len
          if olen != idlen[i]:
            changed = true
          result.add rp
        for i in 0..<n-1:
          if idlen[i] != idlen[i+1]:
            unmatched = true
            break
    of ixkM:
      result.init
      for i in 0..<t.vM.len:
        result.add t.vM[i].matchDummyType s
    of ixkT:
      result.init
      for i in 0..<t.vT.len:
        result.add t.vT[i].matchDummyType s
    of ixkI:
      result.init
    of ixk0:
      result.init
  proc matchDummy(t: var ixtree): replacePairs =
    result.init
    for s in t.alltypes:
      result.add t.matchDummyType s
  # Stitch the functions together.
  var ixt: ixtree
  (result, ixt) = n.replaceDummyU
  if ixt.notempty:
    # hint "contractDummyU:n: " & n.repr
    # hint "contractDummyU:result: " & result.treerepr
    # hint "contractDummyU:ixt: " & ixt.treerepr
    let reps = ixt.matchDummy
    for s in reps:
      result = result.replace s
    let ix = ixt.collectDummy.rmReplaced reps
    result = newStmtList().add(
      newNimNode(nnkVarSection).add(
        newIdentDefs(gensym(nskVar, "__TPL__INTERNAL_REMOVE__"), newEmptyNode(), newLit(0))
      ),
      result
    )
    for i in ix:
      assert i.kind == ixkI
      result[0].add newIdentDefs(i.vId, newCall(bindsym"Dummy", ident($i.vIt)))
macro convertDummyU(n: typed): stmt =
  dbg "convertDummyU <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.contractDummyU
  result = n.g
  dbg "convertDummyU => ", result, TPLDebug.flow

template forIndexCall*[id,lo,hi:static[int]](s, f: expr, i: gTindexDummy[id,lo,hi], body: expr): stmt =
  for s in f(id, lo, hi):
    body
template forIndex*[id,lo,hi:static[int]](s: expr, i: gTindexDummy[id,lo,hi], body: expr): stmt =
  for s in indices(id, lo, hi):
    body
var forDummyId {.compileTime.} = 0
proc dummyLoopGen(ix: seqset[NimNode], n: NimNode): NimNode =
  # echo "dummyLoopGen:n:\n", n.treerepr
  result = n
  for i in ix:
    let id = gensym(nskForVar, "__F" & $forDummyId)
    inc forDummyId
    var body = result.convert(i, id)
    if i.kind == nnkSym:
      result = newCall(bindsym"forIndex", id, i, body)
    elif i.kind in CallNodes and i.len == 2:
      result = newCall(bindsym"forIndexCall", id, ident($i[0]), i[1], body)
    else:
      error "Cannot generate for loops for: " & n.treerepr
  #   echo "dummyLoopGen:", i, ":result:\n", result.treerepr
  # echo "dummyLoopGen:final result\n", result.treerepr
proc indexedTensor(m: NimNode): NimNode =
  var n = m
  if n.kind == nnkHiddenDeref: n = m[0]
  if n.kind in CallNodes and $n[0] in ["[]", "[]="]:
    result = n[1]
  elif n.kind == nnkBracketExpr:
    result = n[0]
  else:                         # What if a HiddenAddr?
    result = newEmptyNode()
var temporaryTensorId {.compileTime.} = 0
macro splitLhsDuplicate(n: typed): stmt =
  dbg "splitLhsDuplicate <= ", n, TPLDebug.flow
  # hint ">>>> splitLhsDuplicate <= " & n.treerepr
  # x[a,b] = y[b]
  #  -> x[a.head,b] = y[b]
  #     x[a.tail,b] = x[a.head,b]
  # NOTE: Skip the last stmt in repeated applications of this macro!
  # echo ">>>> splitLhsduplicate: ", n.lisprepr
  # echo "     ", n.repr
  result = n                    # By default.
  let t = n.genDummyTree
  dbg("dummytree:\n" & t.treerepr, lvl = TPLDebug.detail)
  if n.isAutoSumStmt:
    let
      lhs = n.getlhs
      rhs = n[^1]
      lhsT = lhs.indexedTensor
      rhsT = rhs.indexedTensor
      lhsIx = t.branch.getlhsix
      rhsIx = t.branch[^1].idx
      lhsLocalIx = t.idx - rhsIx
      commonIx = lhsIx - lhsLocalIx
    # echo "lhs:        ", lhs.lisprepr
    # echo "lhsLocalIx: ", lhsLocalIx.repr
    dbg("dummytree:lhsT: " & lhsT.lisprepr, lvl = TPLDebug.detail)
    dbg("dummytree:rhsT: " & rhsT.lisprepr, lvl = TPLDebug.detail)
    if lhsLocalIx.len > 0 and rhs.kind in CallNodes and rhsT == newEmptyNode(): # RHS is not a simple tensor.
      if n.kind == nnkAsgn or (n.kind in CallNodes and $n[0] == "[]="):
        var
          stmtHead = n
          lhsTail = newseq[NimNode](lhsLocalIx.len)
        for m in 0..<lhsTail.len:
          lhsTail[m] = lhs
        for n, i in lhsLocalIx:
          let
            ihead = newCall(bindsym"head", i)
            itail = newCall(bindsym"tail", i)
          stmtHead = stmtHead.convert(i, ihead)
          for m in 0..<lhsTail.len:
            if m < n:
              lhsTail[m] = lhsTail[m].convert(i, ihead)
            elif m == n:
              lhsTail[m] = lhsTail[m].convert(i, itail)
            # Else, for m > n, do nothing.
        result = newStmtList().add(stmtHead)
        for c in lhsTail:
          result.add c.newAssignment stmtHead.getlhs
      else:
        var tt = newNimNode(nnkBracketExpr).add ident("__T" & $temporaryTensorId)
        inc temporaryTensorId
        for i in commonIx:
          tt.add i
        result = newStmtList().add(newCall(bindsym"temporaryTensorEq", tt, rhs))
        result.add n.reAssembleBinOp(lhs, tt)
  dbg "splitLhsduplicate => ", result, TPLDebug.detail
  # hint "<<<< splitLhsDuplicate => " & result.treerepr
macro splitRhsSum(n: typed): stmt =
  dbg "splitRhsSum <= ", n, TPLDebug.flow
  # echo "\n>>>> splitRhsSum <= ", n.repr
  # hint ">>>> splitRhsSum <= " & n.treerepr
  # x[a] = y[a] `op` z[a,b]
  #  -> x[a] = z[a,b]
  #     x[a] = y[a] `op` x[a]
  # x[a,b] = y[a,c] `op` z[b,d]
  #  -> x[a,b] = y[a,c]
  #     x[a,b] `op`= z[b,d]
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      fun = if n.kind == nnkAsgn: "" else: $n[0]
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhs = n[^1]
      rhsT = t.branch[^1]
      rhsIx = rhsT.idx
      lhsLocalIx = t.idx - rhsIx
      rhsLocalIx = t.idx - lhsIx
      rhsOp = if rhs.kind in CallNodes: $rhs[0] else: ""
    if rhs.kind in CallNodes and rhsOp in autoSumOps:
      if rhs.len == 2:          # Unary op.
        if rhsOp == "+":      # We drop it.
          result = n.copy
          result[^1] = rhs[1]
        elif rhsOp == "-":
          if rhs[1].kind in CallNodes and $rhs[1][0] != "[]":
            if n.kind == nnkAsgn or fun == "[]=": # We reuse the lhs.
              result = newStmtList()
              result.add lhs.newAssignment rhs[1]
              result.add lhs.newAssignment lhs.prefix "-"
            elif fun == "+=":
              result = n.copy
              result[0] = bindsym"-="
            elif fun == "-=":
              result = n.copy
              result[0] = bindsym"+="
            elif fun in ["*=", "/="]:
              result = n.copy
              result[^1] = rhs[1]
              result = newStmtList().add(result, lhs.newAssignment lhs.prefix "-")
            else:
              error "AutoSum cannot handle: " & n.repr
          else:                 # For simple rhs, we do nothing.
            result = n
        else:
          error "AutoSum only supports unary '+' and '-'.  Received: " & n.repr
      elif rhs.len == 3:        # Binary op of + - * /.
        let
          lop = rhs[1]
          rop = rhs[2]
          lopIx = rhsT.branch[1].idx
          ropIx = rhsT.branch[2].idx
          lopLocalIx = rhsLocalIx - ropIx
          ropLocalIx = rhsLocalIx - lopIx
        if lopLocalIx.len > 0:  # Hit ROP in the next round of recursion.
          error "not implemented for lopLocalIx.len > 0.  Received: " & n.repr
        elif ropLocalIx.len > 0: # Similar to lopLocalIx.len > 0, but we honor order for "*" and "/".
          error "not implemented for ropLocalIx.len > 0.  Received: " & n.repr
        else:                   # No local index for both operands
          result = n
      else:
        error "AutoSum only supports unary or binary ops.  Received: " & n.repr
    else:               # RHS is not a call to one of autoSumOps.
      result = n
  else:
    result = n
  # hint "<<<< splitRhsSum => " & result.treerepr
macro splitMultiOp(n: typed): stmt =
  dbg "splitMultiOp <= ", n, TPLDebug.flow
  # echo "\n>>>> splitMultiOp <= ", n.repr
  result = n
  # echo "<<<< splitMultiOp => ", result.repr
proc accumulateAutoSum(n: NimNode): NimNode =
  # echo "\n>>>> accumulateAutoSum <= ", n.repr
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      fun = if n.kind == nnkAsgn: "" else: $n[0]
      lhs = n.getlhs
      rhs = n[^1]
      lhsIx = t.branch.getlhsix
      rhsLocalIx = t.idx - lhsIx
    if n.kind == nnkAsgn or fun == "[]=":
      var
        stmtHead = n
        accum = newseq[NimNode](rhsLocalIx.len)
      for m in 0..<accum.len:
        accum[m] = infix(lhs, "+=", rhs)
      for n, i in rhsLocalIx:
        let
          ihead = newCall(bindsym"head", i)
          itail = newCall(bindsym"tail", i)
        stmtHead = stmtHead.convert(i, ihead)
        for m in 0..<accum.len:
          if m < n:
            accum[m] = accum[m].convert(i, ihead)
          elif m == n:
            accum[m] = accum[m].convert(i, itail)
          # Else, for m > n, do nothing.
      result = newStmtList().add(stmtHead)
      for c in accum:
        result.add c
    elif fun in ["*=", "/="]: # Need a temporary.
      error "not implemented for *= or /="
    else:                     # += or -= need no special treatment.
      result = n
  else:
    result = n
  # echo "<<<< accumulateAutoSum => ", result.repr
macro fixpoint(i: static[int], m, oldn, n: typed): stmt =
  # Call m repeatedly on n until nothing changes, with each step
  # type checked.  Requires m accepting a typed.
  # let ii = i.intVal
  # hint "fixpoint:" & m.repr & ":" & $i & " -----> " & n.treerepr
  if i == 0 or oldn != n:
    result = newCall(bindsym"fixpoint", newLit(i+1), m, n, newCall(m, n))
  else:
    result = n
template fixpointcall(m, n: typed): stmt =
  fixpoint(0, m, newEmptyNode(), n)
macro splittingHelper(n: typed): stmt =
  # const splits = @[bindsym"splitLhsDuplicate", bindsym"splitRhsSum", bindsym"splitMultiOp"]
  template splits(n: untyped): stmt =
    splitMultiOp splitRhsSum splitLhsDuplicate n
  proc g(n: NimNode): NimNode =
    # echo "\n## splittingHelper:g <= ", n.treerepr
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockStmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n.copy
      result[6] = result[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.copy # We CANNOT modify n because fixpoint use it.
      # if n.kind == nnkInfix and n[0].kind == nnkSym:
      if n.kind in CallNodes:
        # result[0] = ident($result[0])
        if result[1].kind != nnkPar:
          result[1] = result[1].newPar # Otherwise fails type check?!
        # result[2] = result[2].newPar
      result = getast(splits(result))
      # for t in splits:
      #   result = newCall(t, result)
    # echo "## splittingHelper:g => ", result.treerepr
  # result = bindsym"splitMultiOp".g bindsym"splitRhsSum".g bindsym"splitLhsDuplicate".g n
  result = n.g
  # hint "## splittingHelper: " & result.treerepr
template splitting(n: typed): stmt =
  fixpointcall(splittingHelper, n)
macro autoSum(n: typed): stmt =
  dbg "autoSum <= ", n, TPLDebug.flow
  # hint ">>>> autoSum <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.accumulateAutoSum
  result = n.g
  # hint "<<<< autoSum => " & result.treerepr
proc loopDummy(n: NimNode): NimNode =
  let
    t = n.genDummyTree
    lhsIx = t.branch.getlhsix
    rhsLocalIx = t.idx - lhsIx
    otherIx = t.idx - rhsLocalIx
  # echo "==== n: ", n.treerepr
  # echo "---- t: ", t.treerepr
  result = rhsLocalIx.dummyLoopGen otherIx.dummyLoopGen n
macro looping(n: typed): stmt =
  dbg "looping <= ", n, TPLDebug.flow
  # hint ">>>> looping: <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    # echo "\n>>>> looping:g <= ", n.repr
    if n.kind == nnkStmtList:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.loopDummy
      # let
      #   t = n.genDummyTree
      #   lhsIx = t.branch.getlhsix
      #   rhsLocalIx = t.idx - lhsIx
      #   otherIx = t.idx - rhsLocalIx
      # # echo t.treerepr
      # result = rhsLocalIx.dummyLoopGen otherIx.dummyLoopGen n
    # echo "<<<< looping:g => ", result.repr
  result = n.g
  # hint "<<<< looping => " & result.treerepr
  dbg "looping => ", result, TPLDebug.detail
macro cleanup(n: typed): stmt =
  dbg "cleanup <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    # echo "\n>>>> cleanup:g <= ", n.treerepr
    if n.kind == nnkStmtList:
      result = newStmtList()
      for c in n:
        # Skip varsection with the magic string.
        if c.kind != nnkVarSection or $c[0][0] != "__TPL__INTERNAL_REMOVE__":
          if c.kind == nnkStmtList: # Flatten out nested stmtlist.
            for cc in c.g:
              result.add cc
          else:
            result.add c.g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind == nnkForStmt:
      result = n
      result[^1] = n[^1].g
    else:
      result = n
  result = n.g
  dbg "cleanup => ", result, TPLDebug.detail
macro fusionHelper(n: typed): stmt =
  dbg "fusion <= ", n, TPLDebug.flow
  # hint ">>>> fusion <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    # echo "#### fusion:g <= ", n.repr
    if n.kind == nnkStmtList:
      result = newStmtList()
      var i = 0
      while i < n.len:
        let
          fst = n[i]
          snd = if i < n.len-1: n[i+1] else: newEmptyNode()
        if fst.kind == nnkForStmt and snd.kind == nnkForStmt and
           fst.len == snd.len and fst[^2] == snd[^2]: # ^2 is loop range.
          var forstmt = newNimNode(nnkForStmt)
          for j in 0..<fst.len-1:
            forstmt.add fst[j]
          var sndBody = snd[^1].copy
          for j in 0..<snd.len-2: # All loop variables.
            sndBody = sndBody.replace(snd[j], fst[j])
          var forBody = newStmtList()
          if fst[^1].kind == nnkStmtList:
            for c in fst[^1]:
              forBody.add c.copy # Require this copy to avoid illegal storage access.
          else:
            forBody.add fst[^1]
          if sndBody.kind == nnkStmtList:
            for c in sndBody:
              forBody.add c.copy # Require this copy to avoid illegal storage access.
          else:
            forBody.add sndBody
          for j in 0..<forBody.len: # Still need to make it recheck types.
            if forBody[j].kind in CallNodes and forBody[j][0].kind == nnkSym:
              # forBody[j][0] = ident($forBody[j][0])
              if forBody[j][1].kind != nnkPar:
                forBody[j][1] = forBody[j][1].newPar
              # for k in 1..<forBody[j].len:
              #   if forBody[j][k].kind != nnkPar:
              #     forBody[j][k] = forBody[j][k].newPar
          forstmt.add forBody.g
          result.add forstmt
          inc i, 2
        else:
          result.add fst.g
          inc i
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n.copy
      result[6] = n[6].g
    elif n.kind == nnkForStmt:
      result = newNimNode(nnkForStmt)
      for j in 0..<n.len-1:
        result.add n[j]
      if n[^1].kind in {nnkStmtList, nnkForStmt}:
        result.add n[^1].g
      elif n[^1].kind in CallNodes:
        result.add n[^1].copy   # We don't change n.
        if result[^1].len > 1 and result[^1][1].kind != nnkPar:
          result[^1][1] = result[^1][1].newPar # Another ODD workaround for type mismatch.
      else:
        result.add n[^1]
    else:
      result = n
    # echo "<<<< fusion:g => ", result.repr
  result = n.g
  # hint "<<<< fusion => " & result.treerepr
  dbg "fusion => ", result, TPLDebug.detail
template fusion(n: typed): stmt =
  fixpointcall(fusionHelper, n)
macro showFinal(s: string, n: typed): stmt =
  dbg s.strval, n, TPLDebug.final
  result = n
macro showOutput(s: string, n: typed): stmt =
  dbg s.strval, n, TPLDebug.output
  result = n
macro showCallResult(n: untyped): stmt =
  proc g(n: NimNode): NimNode =
    if n.kind in CallNodes and n.len == 2:
      result = n.copyNimNode
      result.add n[0]
      result.add n[1].g
      result = newCall(bindsym"showOutput", newlit($n[0] & " => "), result)
    elif n.kind == nnkStmtList and n.len == 1 and n[0].kind in CallNodes:
      result = n[0].g
    else:
      result = n
  result = newCall(bindsym"showFinal", newLit" => ", n.g)
macro withDbgLevel(verbose: static[TPLDebug], n: untyped): stmt =
  template g(v: TPLDebug, n: untyped): stmt =
    static:
      const OldLvl = TPLDebugLevel
      TPLDebugLevel = TPLDebug(v)
    n
    static:
      TPLDebugLevel = OldLvl
  result = getast g(verbose, n)
template tensorOpsHelper(v: TPLDebug, n: untyped): stmt =
  withDbgLevel TPLDebug(v):
    showCallResult fusion cleanup looping autoSum splitting convertDummyU reAssign n
proc tensorOpsWithDbgLevel(v: TPLDebug, n: NimNode): NimNode =
  if n.kind in RoutineNodes:
    result = n
    result[6] = getast tensorOpsHelper(v, n[6])
  else:
    result = getast tensorOpsHelper(v, n)
macro tensorOps*(n: untyped): stmt =
  result = tensorOpsWithDbgLevel(TPLDebug.final, n)
macro tensorOpsTrace*(verbose: static[TPLDebug], n: untyped): stmt =
  result = tensorOpsWithDbgLevel(verbose, n)
macro tensorOpsSilent*(n: untyped): stmt =
  result = tensorOpsWithDbgLevel(TPLDebug.none, n)

proc `$`*[D,V;id1,lo1,hi1:static[int]](v: gT1[D,V,id1,lo1,hi1]): string {.tensorOpsSilent.} =
  var i: Dummy(IndexType(v, 1))
  result = ""
  if i == i.type.lo:
    result = "["
  else:
    result &= "\t"
  result &= $v[i]
  if i < i.type.hi:
    result &= ","
  else:
    result &= "\t]"
proc `$`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](m: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): string {.tensorOpsSilent.} =
  var
    i: Dummy(IndexType(m, 1))
    j: Dummy(IndexType(m, 2))
    # k: Dummy(IndexType(m, 0)) # compile time error: out of bounds
  result = ""
  if i == i.type.lo:
    if j == j.type.lo:
      result &= "[[ "
    else:
      result &= "\n [ "
  else:
    result &= "\t"
  result &= $m[i,j]
  if i < i.type.hi:
    result &= ","
  else:
    result &= "\t]"
    if j == j.type.hi:
      result &= "]"
