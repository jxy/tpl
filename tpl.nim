import macros
import seqset
import utils
import tensor_data_default
import strutils

export tensor_data_default.`[]`
export tensor_data_default.`[]=`

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
    elif n.kind in StmtNodes and n.len == 1 and n[0].kind in CallNodes:
      result = n[0].g
    else:
      result = n
  result = newCall(bindsym"showFinal", newLit" => ", n.g)

####################
# index type
type
  # Ideally `AnyIndex` would be a type class to simply the
  # complexity of defining indexing procedures with all the
  # possible index types (O(e^n) definitions for rank-n tensor if
  # defined separately for each index type).  The type class of
  # generic types does not work reliably in Nim now, so we use an
  # extra static type parameters to differentiate different index
  # types, while maintaining the ability to refer to all the
  # index types with this generic type.
  AnyIndex[ty:static[TPLIndex],id,lo,hi:static[int]] = object {.requiresInit.}
    # `ty` is the type of the index.
    # `value` auto inits to 0, which is bad
    # `requiresInit` in v0.13 gives warning without an explicit initialization
    value: int
  TPLIndex {.pure.} = enum
    raw, index, dummy
type
  gTindexUninitialized[id,lo,hi:static[int]] = AnyIndex[TPLIndex.raw,id,lo,hi]
  gTindex[id,lo,hi:static[int]] = AnyIndex[TPLIndex.index,id,lo,hi]
converter idx2int*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): int = i.value
converter idx2float*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): float = i.value.float
iterator indices(id, lo, hi: static[int]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
  var i = gTindex[cid,clo,chi](value: lo)
  while true:
    yield i
    if i.value == hi: break
    inc i.value
iterator items*[ty:static[TPLIndex];id,lo,hi:static[int]](t: typedesc[AnyIndex[ty,id,lo,hi]]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
  var i = gTindex[cid,clo,chi](value: lo)
  while true:
    yield i
    if i.value == hi: break
    inc i.value
proc `$`*[id,lo,hi:static[int]](x: gTindex[id,lo,hi]): string =
  $x.value & ":Idx[" & $id & "," & $lo & "," & $hi & "]"

var IndexID {.compileTime.} = 0
macro IndexType*(lo, hi: static[int]): expr =
  result = newNimNode(nnkBracketExpr).add(
    bindsym"gTindexUninitialized", IndexId.newlit, lo.newlit, hi.newlit)
  inc IndexId
  # hint "IndexType => " & result.lisprepr

template staticInbound(n, lo, hi: static[int]): expr =
  static:
    if n < lo or n > hi:
      error "index out of bounds: " & $n

proc indexValue[id,lo,hi:static[int]](ix: gTindex[id,lo,hi]): int {.inline.} = ix.value

proc index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:typedesc[AnyIndex[ty,id,lo,hi]], n:static[int]): gTindex[id,lo,hi] {.inline.} =
  n.staticInbound lo, hi
  result = type(result)(value: n)
template index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:typedesc[AnyIndex[ty,id,lo,hi]]): expr =
  index(t, lo)
template index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:AnyIndex[ty,id,lo,hi]): expr =
  index(type(t), lo)
template index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:AnyIndex[ty,id,lo,hi], n:static[int]): expr =
  index(type(t), n)

proc `index=`*[id,lo,hi:static[int]](ix:var gTindex[id,lo,hi], n:static[int]) {.inline.} =
  n.staticInbound lo, hi
  ix.value = n

macro nthIndex(n: static[int], ixnums: varargs[int]): expr =
  # echo "nthIndex <= ", $n, ", ", ixnums.repr
  if n >= 1 and n <= ixnums.len div 3:
    result = newNimNode(nnkBracketExpr).add bindsym"gTindex"
    for i in 3*(n-1) .. 3*n-1:
      # echo i
      result.add ixnums[i]
  else:
    error "Index number, " & $n & ", out of range [1," & $(ixnums.len div 3) & "]"
  # echo "nthIndex => ", result.lisprepr

####################
# tensor types

# Rank-0 scalar:
template tensorType(container, element: typedesc): expr =
  element
# Generate rank-n tensors:
proc genTensor(n: int): NimNode {.compileTime.} =
  let
    tType = ident("gT" & $n)
    E = newEmptyNode()
    D = ident"Container"
    V = ident"Element"
  const IxParam = ["id", "lo", "hi"]
  template addIxParams(n: NimNode, i: int): stmt =
    for ix in IxParam:
      n.add ident(ix & $i)
  # Generic Param: [D,V;idI,loI,hiI,...:static[int]]
  var gParam = newNimNode(nnkGenericParams)
  gParam.add newNimNode(nnkIdentDefs).add(D, V, E, E)
  gParam.add newNimNode(nnkIdentDefs)
  for i in 1..n:
    gParam[1].addIxParams i
  gParam[1].add(newNimNode(nnkStaticTy).add(ident"int"), E)
  # Full tensor type: gTN[D,V,idI,loI,hiI,...]
  var tTypeFull = newNimNode(nnkBracketExpr).add(tType, D, V)
  for i in 1..n:
    tTypeFull.addIxParams i
  # Full tensor index type: AnyIndex[tyN,idN,loN,hiN]
  proc iTypeAny(n: int): NimNode {.compileTime.} =
    result = newNimNode(nnkBracketExpr).add(ident"AnyIndex", ident("ty" & $n))
    result.addIxParams n
  result = newStmtList()
  # Tensor type definition
  block:
    let objT = newNimNode(nnkObjectTy).add(
      E, E, newNimNode(nnkRecList).add(
        newNimNode(nnkIdentDefs).add(
          ident"data".postfix("*"), D, E)))
    result.add newNimNode(nnkTypeSection).add newNimNode(nnkTypeDef).add(tType, gParam, objT)
  # Template to generate a Tensor type
  block:
    var
      fParam = newNimNode(nnkFormalParams).add(
        ident"expr",
        newNimNode(nnkIdentDefs).add(D, V, ident"typedesc", E),
        newNimNode(nnkIdentDefs))
      body = newStmtList().add(newNimNode(nnkConstSection), tTypeFull)
    for i in 1..n:
      fParam[2].add ident("i" & $i)
      for ix in IxParam:
        body[0].add newNimNode(nnkConstDef).add(
          ident(ix & $i),
          E,
          newDotExpr(ident("i" & $i), ident(ix)))
    fParam[2].add(ident"typedesc", E)
    result.add newNimNode(nnkTemplateDef).add(
      ident"tensorType", E, E, fParam, E, E, body)
  # Template to obtain a index type from a tensor
  block:
    let
      tensor = ident"tensor"
      nIndex = ident"nIndex"
      fParam = newNimNode(nnkFormalParams).add(
        ident"expr",
        newIdentDefs(tensor, tTypeFull),
        newIdentDefs(nIndex, ident"int"))
    var
      body = newCall(bindsym"nthIndex", nIndex)
    for i in 1..n:
      body.addIxParams i
    result.add newNimNode(nnkTemplateDef).add(
      ident"IndexType".postfix("*"), E, gParam, fParam, E, E, body)
  # Indexing procs
  block:
    let
      X = ident"x"
      Y = ident"y"
      procName = newNimNode(nnkAccQuoted).add(ident"[]").postfix "*"
    var
      # fParam = newNimNode(nnkFormalParams).add(V, newIdentDefs(X, tTypeFull))
      fParam = newNimNode(nnkFormalParams).add(ident"expr", newIdentDefs(X, tTypeFull))
      body = newNimNode(nnkBracketExpr).add(X.newDotExpr ident"data")
    for i in 1..n:
      fParam.add newIdentDefs(ident("i" & $i), iTypeAny(i))
      # body.add newDotExpr(ident("i" & $i), ident"i")
      body.add newCall(bindsym"indexValue", ident("i" & $i))
    # let procIx = newNimNode(nnkProcDef).add(
    #   procName, E, gParam, fParam,
    #   newNimNode(nnkPragma).add(ident"inline"), E, newStmtList().add body)
    var gParamAny = gParam.copy
    gParamAny.add newNimNode(nnkIdentDefs)
    for i in 1..n:
      gParamAny[^1].add ident("ty" & $i)
    gParamAny[^1].add(newNimNode(nnkStaticTy).add(ident"TPLIndex"), E)
    let procIx = newNimNode(nnkTemplateDef).add(
      procName, E, gParamAny, fParam, E, E, newStmtList body)
    # var procVIx = procIx.copy
    # [3] is FormalParams of a ProcDef
    # procVIx[3][0] = newNimNode(nnkVarTy).add V # Return type.
    # procVIx[3][1][1] = newNimNode(nnkVarTy).add tTypeFull # Type of X.
    # var procIxEq = procVIx.copy
    var procIxEq = procIx.copy
    procIxEq[0][1][0] = ident"[]=" # Proc name.
    # procIxEq[3][0] = E
    procIxEq[3].add newIdentDefs(Y, V)
    procIxEq[6][0] = newAssignment(procIxEq[6][0], Y)
    # result.add(procIx, procVIx, procIxEq)
    result.add(procIx, procIxEq)
macro genTensors(n: static[int]): stmt =
  result = newStmtList()
  for i in 1..n:
    for c in genTensor(i):
      result.add c
  # We `copy` complex structures to avoid some vm bugs.
  result = result.copy
  # echo "genTensors(", n, ") =>\n", result.repr
const maxTensorRanks = 16
genTensors(maxTensorRanks)

proc addDot(d: var NimNode, i: NimNode, id: varargs[string]) =
  for s in id:
    d.add(i.newDotExpr s.ident)

proc genTensorType(container, element, index: NimNode): NimNode =
  result = newCall(bindsym"tensorType", container, element)
  for i in index:
    result.add i
  # echo "<<<< genTensortype => ", result.lisprepr
macro Tensor*(index: openarray[untyped], element, container: untyped): expr =
  result = genTensorType(container, element, index)
macro Tensor*(index: openarray[untyped], element: untyped): expr =
  var container = newCall(bindsym"TensorDataDefault", element)
  for i in index:
    container.addDot(i, "lo", "hi")
  result = genTensorType(container, element, index)

####################
# dummy index type
type
  gTindexDummy[id,lo,hi:static[int]] = AnyIndex[TPLIndex.dummy,id,lo,hi]
converter TPLDummyConv*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): gTindex[id,lo,hi] {.nodecl.} = index(i)
converter TPLDummyConv*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): int {.nodecl.} = discard
converter TPLDummyConv*[id,lo,hi:static[int]](i: gTindexDummy[id,lo,hi]): float {.nodecl.} = discard
proc dummyFromConverter(n: NimNode): NimNode =
  if n.kind in CallNodes and n[0].kind == nnkSym and "TPLDummyConv" == $n[0]:
    let
      f = n[0].symbol.getimpl
      t = f[3][1][1]
    # echo "call type: ", n[0].gettype.lisprepr
    # echo "call Impl:\n", f.treerepr
    if f.kind == nnkConverterDef and
       ((t[0] == bindsym"AnyIndex" and t[1].intval == int(TPLIndex.dummy)) or
        t[0] == bindsym"gTindexDummy"):
      result = n[1]
    else:
      error "dummyFromConverter got:\n" & n.treerepr & "\nwith f:\n" & f.repr & "\nparameter type: " & t.lisprepr
  # echo "dummyFromConverter: => ", result.lisprepr

proc dummy*[ty:static[TPLIndex];id,lo,hi:static[int]](t: typedesc[AnyIndex[ty,id,lo,hi]]): gTindexDummy[id,lo,hi] =
  result = type(result)(value: lo)
proc dummy*[ty:static[TPLIndex];id,lo,hi:static[int]](t: AnyIndex[ty,id,lo,hi]): gTindexDummy[id,lo,hi] =
  result = type(result)(value: lo)
proc dummyIx(id,lo,hi: static[int]): gTindexDummy[id,lo,hi] =
  result = type(result)(value: lo)

iterator items*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
  var i = gTindex[cid,clo,chi](value: clo)
  while true:
    yield i
    if i.value == chi: break
    inc i.value
template head*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): gTindex[id,lo,hi] =
  # This `index` call is also a template that gets expanded
  # leaving no trace of the variable `t`.
  index(t, lo)
iterator tail*(id, lo, hi: static[int]): gTindex[id,lo,hi] =
  const
    cid = id
    clo = lo
    chi = hi
    lo1 = lo + 1
  if lo1 <= hi:
    var i = gTindex[cid,clo,chi](value: lo1)
    while true:
      yield i
      if i.value == hi: break
      inc i.value
proc tail*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): gTindexDummy[id,lo,hi] {.nodecl.} = t

template index*[id,lo,hi:static[int]](d:gTindexDummy[id,lo,hi], n:static[int]): expr =
  index(gTindex[id,lo,hi], n)

####################
# Automatic dummy index
proc automaticIndex(id, lo, hi: static[int]): gTindexDummy[id,lo,hi] {.nodecl.} =
  dummyIx(id, lo, hi)

macro indexingT2I1(x: typed;
                   id1, lo1, hi1, id2, lo2, hi2: int;
                   i1: typed; i1id, i1lo, i1hi: int): expr =
  if id1.intval == i1id.intval and lo1.intval == i1lo.intval and hi1.intval == i1hi.intval and
     id2.intval == i1id.intval and lo2.intval == i1lo.intval and hi2.intval == i1hi.intval:
    error "Ambiguous indexing for: " & x.repr & "[" & i1.repr & "]"
  elif id1.intval == i1id.intval and lo1.intval == i1lo.intval and hi1.intval == i1hi.intval:
    result = newCall("[]", x, i1, newCall(bindsym"automaticIndex", id2, lo2, hi2))
  elif id2.intval == i1id.intval and lo2.intval == i1lo.intval and hi2.intval == i1hi.intval:
    result = newCall("[]", x, newCall(bindsym"automaticIndex", id1, lo1, hi1), i1)
  else:
    error "Indexing fails for: " & x.repr & "[" & i1.repr & "]"
macro indexingEqT2I1(x: typed;
                     id1, lo1, hi1, id2, lo2, hi2: int;
                     i1: typed; i1id, i1lo, i1hi: int;
                     y: typed): expr =
  if id1.intval == i1id.intval and lo1.intval == i1lo.intval and hi1.intval == i1hi.intval and
     id2.intval == i1id.intval and lo2.intval == i1lo.intval and hi2.intval == i1hi.intval:
    error "Ambiguous indexing for: " & x.repr & "[" & i1.repr & "]=" & y.repr
  elif id1.intval == i1id.intval and lo1.intval == i1lo.intval and hi1.intval == i1hi.intval:
    result = newCall("[]=", x, i1, newCall(bindsym"automaticIndex", id2, lo2, hi2), y)
  elif id2.intval == i1id.intval and lo2.intval == i1lo.intval and hi2.intval == i1hi.intval:
    result = newCall("[]=", x, newCall(bindsym"automaticIndex", id1, lo1, hi1), i1, y)
  else:
    error "Indexing fails for: " & x.repr & "[" & i1.repr & "]=" & y.repr
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: AnyIndex[i1ty,i1id,i1lo,i1hi]): expr =
  indexingT2I1(x, id1, lo1, hi1, id2, lo2, hi2, i1, i1id, i1lo, i1hi)
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], y: V): expr =
  indexingEqT2I1(x, id1, lo1, hi1, id2, lo2, hi2, i1, i1id, i1lo, i1hi, y)

template genUnaryOp(op: untyped): stmt =
  template op*[D,V;id1,lo1,hi1:static[int]](x: gT1[D,V,id1,lo1,hi1]): expr =
    op(x[automaticIndex(id1,lo1,hi1)])
  template op*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): expr =
    op(x[automaticIndex(id1,lo1,hi1), automaticIndex(id2,lo2,hi2)])

macro genUOp(os: varargs[untyped]): stmt =
  result = newStmtList()
  for o in os:
    result.add newCall(bindsym"genUnaryOp", o)
genUOp(`+`, `-`)

template genBinaryOp(op: untyped): stmt =
  template op*[lD,lV;lid1,llo1,lhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: lV): expr =
    op(x[automaticIndex(lid1,llo1,lhi1)], y)
  template op*[rD,rV;rid1,rlo1,rhi1:static[int]](x: rV, y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
    op(x, y[automaticIndex(rid1,rlo1,rhi1)])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
    op(x[automaticIndex(lid1,llo1,lhi1)], y[automaticIndex(rid1,rlo1,rhi1)])
  template op*[lD,lV;lid1,llo1,lhi1,lid2,llo2,lhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: lV): expr =
    op(x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)], y)
  template op*[rD,rV;rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: rV, y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
    op(x, y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
    op(x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)], y[automaticIndex(rid1,rlo1,rhi1)])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
    op(x[automaticIndex(lid1,llo1,lhi1)], y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)])
  template op*[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
    op(x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)], y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)])

macro genBOp(os: varargs[untyped]): stmt =
  result = newStmtList()
  for o in os:
    result.add newCall(bindsym"genBinaryOp", o)
genBOp(`+`, `-`, `*`, `/`, `+=`, `-=`, `*=`, `/=`)

template autoIndexAsgn[lD,lV;lid1,llo1,lhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: lV): expr =
  x[automaticIndex(lid1,llo1,lhi1)] = y
template autoIndexAsgn[rD,rV;rid1,rlo1,rhi1:static[int]](x: rV, y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
  x = y[automaticIndex(rid1,rlo1,rhi1)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
  x[automaticIndex(lid1,llo1,lhi1)] = y[automaticIndex(rid1,rlo1,rhi1)]
template autoIndexAsgn[lD,lV;lid1,llo1,lhi1,lid2,llo2,lhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: lV): expr =
  x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)] = y
template autoIndexAsgn[rD,rV;rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: rV, y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
  x = y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT1[rD,rV,rid1,rlo1,rhi1]): expr =
  x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)] = y[automaticIndex(rid1,rlo1,rhi1)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
  x[automaticIndex(lid1,llo1,lhi1)] = y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): expr =
  x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)] = y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)]
macro autoIndexAsgn[T](lhs: T, rhs: T): stmt =
  dbg "autoIndexAsgn <= lhs: ", lhs, TPLDebug.detail
  dbg "autoIndexAsgn <= rhs: ", rhs, TPLDebug.detail
  var lhs = lhs.unwrap
  if lhs.kind in CallNodes and $lhs[0] == "[]": # Indexing operation
    result = newNimNode(nnkBracketExpr)
    # result = newCall(ident"[]=")
    for i in 1..<lhs.len:
      result.add lhs[i]
  else:
    result = lhs
  result = wrappedAssign(result, rhs)
  dbg "autoIndexAsgn => ", result, TPLDebug.detail

####################
# tensor ops
proc newTensorAssign(lhs, rhs: NimNode): NimNode =
  # Use `+=`, assuming new tensors are initialized with 0.
  if lhs.len == 1:
    result = infix(lhs[0], "+=", rhs)
  elif lhs.len > 1:
    result = infix(lhs, "+=", rhs)
  else:
    error "Don't know how to assign rhs: " & rhs.treerepr & " to lhs: " & lhs.treerepr
macro defTensorEq(lhs: untyped, rhs: typed): stmt =
  dbg "defTensorEq:lhs: ", lhs, TPLDebug.detail
  dbg "defTensorEq:rhs: ", rhs, TPLDebug.detail
  result = newStmtList().add(newNimNode(nnkVarSection), newTensorAssign(lhs, rhs))
  let rhsT = newCall(bindsym"type", rhs)
  if lhs.kind == nnkBracketExpr:
    if lhs.len > 1:
      var tensorCall = newCall(bindsym"Tensor", newNimNode(nnkBracket), rhsT)
      for i in 1..<lhs.len:
        tensorCall[1].add newCall(bindsym"type", lhs[i])
      result[0].add newIdentDefs(lhs[0], tensorCall)
    elif lhs.len == 1:
      result[0].add newIdentDefs(lhs[0], rhsT)
    else:
      error "Don't know how to create temporaryTensor from lhs: '" & lhs.repr & "' and rhs: '" & rhs.repr & "'"
  elif lhs.kind == nnkIdent or lhs.kind == nnkSym:
    result[0].add newIdentDefs(lhs, rhsT)
  else:
    error "Don't know how to create temporaryTensor from lhs: '" & lhs.repr & "' and rhs: '" & rhs.repr & "'"
  dbg "defTensorEq:result => ", result, TPLDebug.detail

macro staticforbody(i: untyped, j: int, t: typed, n: untyped): untyped =
  # echo "\n>>>> staticfor"
  let
    ix = newCall(bindsym"index", t, j)
  result = replace(n, i, ix)
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< staticfor"
template staticforindex*[ty:static[TPLIndex];id,lo,hi:static[int]](i: untyped, t: typedesc[AnyIndex[ty,id,lo,hi]], n: untyped): expr =
  unrollfor j, lo, hi:
    staticforbody(i, j, t, n)
template staticforindex*[ty:static[TPLIndex];id,lo,hi:static[int]](i: untyped, t: AnyIndex[ty,id,lo,hi], n: untyped): expr =
  unrollfor j, lo, hi:
    staticforbody(i, j, type(t), n)
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
    let d = n.dummyFromConverter
    if d.kind != nnkNilLit:
      # echo "   result.idx: ", result.idx.repr
      # echo "-- dummy: ", n.lisprepr
      result.idx.incl d
      # echo "   result.idx: ", result.idx.repr
    else:
      # echo "subtree result.idx: ", result.idx.repr
      for i, c in n:
        let t = if n.skipDummyCheck i: newEmptyNode().g else: c.g
        result.idx += t.idx
        # echo "     += ", t.idx.repr
        # echo "        result.idx: ", result.idx.repr
        result.branch[i] = t
      # echo "subtree result.idx: ", result.idx.repr
  result = n.g
  # echo "<<<< genDummytree =>\n", result.treerepr

const autoSumFunctions = ["=", "+=", "-=", "*=", "/=", "[]="]
const autoSumFunctionNoBracket = ["=", "+=", "-=", "*=", "/="]
const autoSumOps = ["+", "-", "*", "/"]

proc getlhs(n: NimNode): NimNode =
  # echo "getlhs: ", n.treerepr
  if n.kind == nnkAsgn:
    result = n[0]
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
proc getrhsix(s: seq[dummyTree]): seqset[NimNode] =
  result.init
  if s.len > 0:
    result.incl s[^1].idx
proc isAutoSumStmt(n: NimNode): bool =
  result = n.kind == nnkAsgn or (n.kind in CallNodes and $n[0] in autoSumFunctions)
proc needAutoSum(n: NimNode, t: dummyTree): bool =
  let rhsLocalIx = t.idx - t.branch.getlhsix
  result = n.isAutoSumStmt and rhsLocalIx.len > 0
proc reAssembleBinOp(n, lhs, rhs: NimNode): NimNode =
  if n.kind == nnkAsgn or
     (n.kind in CallNodes and $n[0] == "[]=" and lhs.kind == nnkBracketExpr):
    result = wrappedAssign(lhs, rhs)
  elif n.kind in CallNodes and n.len == 3:
    result = n.copyNimNode.add(n[0], lhs, rhs.newPar)
    result = result.callNodesWrap
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
    if n.kind in StmtNodes:
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
  dbg "reAssign => ", result, TPLDebug.detail

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
proc contractAutoDummy(n: NimNode): NimNode =
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
  proc replaceAutoDummy(n: NimNode): (NimNode, ixtree) =
    # hint n.lisprepr
    if n.kind in CallNodes and $n[0] == "automaticIndex":
      var t = newPar()
      for i in 1..<n.len:
        t.add n[i]
      let d = gensym(nskVar, "__D" & $dID & "__" & t.dummyStr)
      inc dID
      result = (d, ixtree(kind: ixkI, vId: d, vIt: t))
    elif n.isAutoSumStmt:
      let
        (lhs, lt) = n.getlhs.replaceAutoDummy
        (rhs, rt) = n[^1].replaceAutoDummy
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
        let (r, t) = c.replaceAutoDummy
        nn.add r
        ixt.add t
      if ixt.empty:
        result = (n, ixtree(kind: ixk0))
      else:
        # Special rebindings here to force type check the stmt again.
        if nn.kind in CallNodes:
          nn = nn.callNodesWrap.rebindIndexing
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
  proc matchDummyType(t: var ixtree, s: NimNode): replacePairs # Used in following recursions.
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
  (result, ixt) = n.replaceAutoDummy
  if ixt.notempty:
    # hint "contractAutoDummy:n: " & n.repr
    # hint "contractAutoDummy:result: " & result.treerepr
    # hint "contractAutoDummy:ixt: " & ixt.treerepr
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
      var d = newCall(bindsym"dummyIx")
      for s in i.vIt:
        d.add s
      result[0].add newIdentDefs(i.vId, newEmptyNode(), d)
macro convertAutoDummy(n: typed): stmt =
  dbg "convertAutoDummy <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    if n.kind in StmtNodes:
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
      result = n.contractAutoDummy
  result = n.g
  dbg "convertAutoDummy => ", result, TPLDebug.flow

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
  var n = m.unwrap
  if n.kind in CallNodes and $n[0] in ["[]", "[]="]:
    result = n[1]
  elif n.kind == nnkBracketExpr:
    result = n[0]
  else:                         # What if a HiddenAddr?
    result = newEmptyNode()
var temporaryTensorId {.compileTime.} = 0
proc temporaryTensor(ix: seqset[NimNode], rhs: NimNode): (NimNode, NimNode) =
  # Returns a tensor of BracketExpr[T,ix...] or a scalar of
  # nnkSym, and the definition.
  var tt = newNimNode(nnkBracketExpr).add gensym(nskVar, "__T" & $temporaryTensorId)
  inc temporaryTensorId
  if ix.len > 0:
    for i in ix:
      tt.add i
    result = (tt, newCall(bindsym"defTensorEq", tt, rhs))
  else:
    result = (tt[0], newCall(bindsym"defTensorEq", tt, rhs))
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
          result.add c.wrappedAssign stmtHead.getlhs
      else:
        let (tt, def) = temporaryTensor(commonIx, rhs)
        result = newStmtList(def, n.reAssembleBinOp(lhs, tt))
  dbg "splitLhsDuplicate => ", result, TPLDebug.detail
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
              result.add lhs.wrappedAssign rhs[1]
              result.add lhs.wrappedAssign lhs.prefix "-"
            elif fun == "+=":
              result = n.copy
              result[0] = bindsym"-="
            elif fun == "-=":
              result = n.copy
              result[0] = bindsym"+="
            elif fun in ["*=", "/="]:
              result = n.copy
              result[^1] = rhs[1]
              result = newStmtList(result, lhs.wrappedAssign lhs.prefix "-")
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
          result = newStmtList()
          if (n.kind == nnkAsgn or fun == "[]=") and lopIx in lhsIx: # We reuse the lhs.
            result.add(
              n.reAssembleBinOp(lhs, lop),
              infix(lhs, rhsOp & "=", rop)
            )
          else:
            let (tt, def) = temporaryTensor(lopIx - lopLocalIx, lop)
            result.add(
              def,
              n.reAssembleBinOp(lhs, rhs.reAssembleBinOp(tt, rop))
            )
        elif ropLocalIx.len > 0: # Similar to lopLocalIx.len > 0, but we honor order for "*" and "/".
          result = newStmtList()
          if (n.kind == nnkAsgn or fun == "[]=") and ropIx in lhsIx: # We reuse the lhs.
            result.add n.reAssembleBinOp(lhs, rop)
            if rhsOp in ["+", "-"]:
              result.add infix(lhs, rhsOp & "=", lop)
            else:               # Honor the order if not + or -.
              result.add n.reAssembleBinOp(lhs, rhs.reAssembleBinOp(lop, lhs))
          else:
            let (tt, def) = temporaryTensor(ropIx - ropLocalIx, rop)
            result.add(
              def,
              n.reAssembleBinOp(lhs, rhs.reAssembleBinOp(lop, tt))
            )
        else:                   # No local index for both operands
          result = n
      else:
        error "AutoSum only supports unary or binary ops.  Received: " & n.repr
    else:               # RHS is not a call to one of autoSumOps.
      result = n
  else:
    result = n
  # hint "<<<< splitRhsSum => " & result.treerepr
proc collectTensors(n: NimNode): (seqset[NimNode], seqset[NimNode]) =
  # Returns tensors or scalars in the form of Par(BracketExpr())
  # in two lists: those used as lvalues and those did not.  Note:
  # scalars (symbol not indexed with []) are only returned when
  # they are used as a var (lvalue).
  # echo "collectTensors:n <= # ", n.lisprepr
  proc extractIndex(n: NimNode): NimNode =
    if n.kind in CallNodes and $n[0] == "indexValue":
      result = n[1]
    else:
      result = n
  proc extractTensor(n: NimNode): NimNode =
    if n.kind == nnkDotExpr and $n[1] == "data":
      result = n[0]
    else:
      result = n
  var lv, vl: seqset[NimNode]
  lv.init
  vl.init
  template recurseAdd(nn: NimNode): stmt =
    let (a, b) = nn.collectTensors
    for x in a:
      lv.incl x
    for x in b:
      vl.incl x
  if n.kind == nnkAsgn:
    var nn = n[0].unwrap
    if nn.kind != nnkSym:
      error "Don't know how to extract tensors from: " & nn.treerepr & "\nin: " & n.treerepr
    lv.incl newNimNode(nnkBracketExpr).add nn
    recurseAdd n[0]
    recurseAdd n[1]
  elif n.kind in CallNodes:
    if n[0].kind == nnkSym:
      # echo "collectTensors:n: ", n.repr
      var fp = n[0].symbol.getimpl[3]
      # echo "collectTensors:fp: ", fp.repr
      # if fp[0].kind == nnkVarTy: # Return a var (lvalue).
      #   error "what do we do here?"
      var k = 1
      for i in 1..<fp.len:            # List of params.
        let isVarParam = fp[i][^2].kind == nnkVarTy
        for j in 0..<fp[i].len-2:
          var nkj = n[k+j].unwrap
          if nkj.kind in CallNodes + {nnkConv, nnkStmtListExpr}:
            # Don't care.
            recurseAdd nkj
          elif nkj.kind in {nnkSym, nnkDotExpr}:
            var t = newNimNode(nnkBracketExpr)
            # Add the tensor symbol.
            t.add nkj.extractTensor
            # Add indices.
            if i == 1: # The first argument to [] or []= is the tensor.
              if $n[0] == "[]":
                for m in 2..<n.len:
                  t.add n[m].extractIndex
              if $n[0] == "[]=":
                for m in 2..<n.len-1:
                  t.add n[m].extractIndex
            if isVarParam:
              lv.incl t
            else:
              vl.incl t
          elif nkj.kind in nnkLiterals or
               (nkj.kind == nnkBracketExpr and
                nkj[0].kind == nnkSym and
                $nkj[0].gettype[0] == "typeDesc"):
            discard "We don't need to worry about these."
          else:
            error "Don't know how to extract tensors from: " &
              n.treerepr & "\nwith: " & fp.treerepr &
              "\nlooking at: " & nkj.treerepr
        k.inc(fp[i].len-2)
    else:
      error "Don't know how to extract tensors from: " & n.treerepr
  elif n.kind == nnkBracketExpr:
    var t = n.copy
    for i in 1..<t.len:
      t[i] = t[i].extractIndex
    if n[0].kind in {nnkHiddenAddr, nnkHiddenDeref} and n[0][0].kind in {nnkSym, nnkDotExpr}:
      # FIXME: this check may no longer work if getlhs removes these hidden nodes.
      t[0] = t[0][0].extractTensor
      lv.incl t
    elif n[0].kind in {nnkSym, nnkDotExpr}:
      t[0] = t[0].extractTensor
      vl.incl t
    elif n[0].kind in CallNodes:
      t[0] = t[0].extractTensor
      var fp = n[0][0].symbol.getimpl[3]
      if fp[0].kind == nnkVarTy: # Return a var (lvalue).
        lv.incl t
      else:
        vl.incl t
      for c in n[0]:
        recurseAdd c
    else:
      error "Don't know how to extract tensors from: " & n.treerepr
  else:
    for c in n:
      recurseAdd c
  result = (lv, vl)
  # echo "collectTensors:result => ", result.repr
proc conflictTensor(xs: seqset[NimNode], rs: varargs[seqset[NimNode]]): bool =
  # Nodes are BracketExpr(T,...).  Returns true if any
  # tensor/scalar in xs is used in rs with different indices.
  # WARNING: this check is only reliable when auto summation
  # statements have been split.
  proc g(x: NimNode, r: seqset[NimNode]): bool =
    for y in r:
      if x[0] == y[0] and x != y:
        return true
    return false
  # hint "conflictTensor:xs: " & xs.repr
  # hint "conflictTensor:rs: " & rs.repr
  for x in xs:
    for r in rs:
      if x.g r:
        return true
  return false
proc addRequiredTemporary(n: NimNode): NimNode =
  # Note: the conflict resolution is only reliable when this
  # transformation is performed after fully split auto summation.
  # With current implementation, only stmt that isAutoSumStmt are
  # checked.
  result = n                    # By default.
  if n.isAutoSumStmt:
    let
      t = n.genDummyTree
      fun = if n.kind == nnkAsgn: "" else: $n[0]
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhs = n[^1]
      rhsT = t.branch[^1]
      rhsIx = rhsT.idx
      rhsLocalIx = t.idx - lhsIx
      commonIx = rhsIx - rhsLocalIx
      (lhsl, lhsr) = lhs.collectTensors
      (rhsl, rhsr) = rhs.collectTensors
    # hint "Variables in: " & lhs.repr & "\nwith lvalue: " & lhsl.repr & "\nand rest: " & lhsr.repr
    # hint "Variables in: " & rhs.repr & "\nwith lvalue: " & rhsl.repr & "\nand rest: " & rhsr.repr
    if lhsl.conflictTensor(rhsl, rhsr, lhsr) or
       (needAutoSum(n, t) and fun in ["*=", "/="]):
      let (tt, def) = temporaryTensor(commonIx, rhs)
      result = newStmtList().add(def, n.reAssembleBinOp(lhs, tt))
macro requireTemporary(n: typed): stmt =
  dbg "requireTemporary <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    if n.kind in StmtNodes:
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
      result = n.addRequiredTemporary
  result = n.g
proc accumulateAutoSum(n: NimNode): NimNode =
  # echo "\n>>>> accumulateAutoSum <= ", n.treerepr
  let t = n.genDummyTree
  # echo t.treerepr
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
      error "Internal error: requireTemporary should have dealt with this: " & n.treerepr
    else:                     # += or -= need no special treatment.
      result = n
  else:
    result = n
  # echo "<<<< accumulateAutoSum => ", result.repr
macro fixpoint(i: static[int], m, oldn, n: typed): stmt =
  # Call m repeatedly on n until nothing changes, with each step
  # type checked.  Requires m accepting a typed.
  dbg "fixpoint:" & $m & ":" & $i & " => ", n, TPLDebug.flow
  if i == 0 or oldn != n:
    result = newCall(bindsym"fixpoint", newLit(i+1), m, n, newCall(m, n))
  else:
    result = n
template fixpointcall(m, n: typed): stmt =
  fixpoint(0, m, newEmptyNode(), n)
macro splittingHelper(n: typed): stmt =
  # const splits = @[bindsym"splitLhsDuplicate", bindsym"splitRhsSum"]
  template splits(n: untyped): stmt =
    splitRhsSum splitLhsDuplicate n
  proc g(n: NimNode): NimNode =
    # echo "\n## splittingHelper:g <= ", n.treerepr
    if n.kind in StmtNodes:
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
        result = result.callNodesWrap
      result = getast splits result
    # echo "## splittingHelper:g => ", result.treerepr
  # result = bindsym"splitReqTemp".g bindsym"splitRhsSum".g bindsym"splitLhsDuplicate".g n
  result = n.g
  # hint "## splittingHelper: " & result.treerepr
template splitting(n: typed): stmt =
  fixpointcall(splittingHelper, n)
macro autoSum(n: typed): stmt =
  dbg "autoSum <= ", n, TPLDebug.flow
  # hint ">>>> autoSum <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    if n.kind in StmtNodes:
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
    rhsIx = t.branch.getrhsix
    rhsLocalIx = t.idx - lhsIx
    lhsLocalIx = t.idx - rhsIx
    commonIx = rhsIx - rhsLocalIx
  # echo "loopDummy:\n", t.treerepr
  # for i in t.idx:
  #   echo i.lisprepr
  # echo "AllIx: ", t.idx.repr
  # echo "lhsIx: ", lhsIx.repr
  # echo "rhsIx: ", rhsIx.repr
  # echo "lhsLocalIx: ", lhsLocalIx.repr
  # echo "rhsLocalIx: ", rhsLocalIx.repr
  # echo "commonIx: ", commonIx.repr
  result =
    rhsLocalIx.dummyLoopGen commonIx.dummyLoopGen lhsLocalIx.dummyLoopGen n
macro looping(n: typed): stmt =
  dbg "looping <= ", n, TPLDebug.final
  # hint ">>>> looping: <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    # echo "\n>>>> looping:g <= ", n.repr
    if n.kind in StmtNodes:
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
    if n.kind in StmtNodes:
      result = newStmtList()
      for c in n:
        # Skip varsection with the magic string.
        if c.kind == nnkVarSection and
           $c[0][0] == "__TPL__INTERNAL_REMOVE__":
          continue
        if c.kind == nnkDiscardStmt:
          continue
        if c.kind in StmtNodes: # Flatten out nested stmtlist.
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

proc conflictTensorIndexing(xs: seqset[NimNode], i: NimNode, ys: seqset[NimNode], j: NimNode): bool =
  # Check each tensor/scalar BracketExpr(T,...) in xs, with the
  # same in ys, return true if the index i in xs and j in ys are
  # in different position of the same tensor or two scalar lvalue
  # are the same.
  # echo "conflictTensorIndexing:xs: ", xs.repr
  # echo "conflictTensorIndexing:i: ", i.lisprepr
  # echo "conflictTensorIndexing:ys: ", ys.repr
  # echo "conflictTensorIndexing:j: ", j.lisprepr
  result = false
  for x in xs:
    for y in ys:
      if x[0] == y[0]:
        result = true           # Conflict by default.
        if x.len == y.len and x.len > 1:
          for k in 1..<x.len:
            if x[k] == i and y[k] == j: # Both indexing the same.
              result = false
            elif x[k] == i or y[k] == j: # One but not the other.
              result = true
        if result:              # Return if conflict.
          return

proc isFirstAssignedTo(x, n: NimNode): bool =
  proc g(n: NimNode): int =
    # 0: Not found; 1: true; -1: false
    for c in n:
      if c.kind == nnkSym and c == x:
        return -1
      elif c.kind == nnkAsgn:
        var lhs = c[0].unwrap
        if lhs == x:
          return 1
        else:
          for k in c:
            let r = k.g
            if r != 0:
              return r
      else:
        let r = c.g
        if r != 0:
          return r
    return 0
  let r = n.g
  if r > 0:
    result = true
  elif r < 0:
    result = false
  else:
    error "Didn't find the symbol: " & x.treerepr & "\nin: " & n.treerepr
proc safeLoopFusion(fst, snd: NimNode): bool =
  # echo "safeLoopFusion:fst <= ", fst.repr
  # echo "safeLoopFusion:snd <= ", snd.repr
  result = true
  var
    (lhs1, rhs1) = fst.collectTensors
    (lhs2, rhs2) = snd.collectTensors
  # echo "safeLoopFusion:lhs1: ", lhs1.repr
  # echo "safeLoopFusion:rhs1: ", rhs1.repr
  # echo "safeLoopFusion:lhs2: ", lhs2.repr
  # echo "safeLoopFusion:rhs2: ", rhs2.repr

  # Special treatment for scalars.  If a scalar is assigned to at
  # it's first use in fst, and then used in snd, it does not lead
  # to conflict.
  var xs: type(lhs1)
  xs.init
  for x in lhs1:
    if x.len == 1 and x[0].kind == nnkSym and x[0].isFirstAssignedTo fst:
        xs.incl x
  for i in 0..<fst.len-2:       # All loop variables.
    result = result and not conflictTensorIndexing(lhs1, fst[i], lhs2, snd[i])
    result = result and not conflictTensorIndexing(lhs1, fst[i], rhs2, snd[i])
    result = result and not conflictTensorIndexing(rhs1, fst[i], lhs2, snd[i])

macro fusionHelper(n: typed): stmt =
  dbg "fusion <= ", n, TPLDebug.flow
  # hint ">>>> fusion <= " & n.treerepr
  proc g(n: NimNode): NimNode =
    # echo "#### fusion:g <= ", n.repr
    if n.kind in StmtNodes:
      result = newStmtList()
      var i = 0
      while i < n.len:
        let
          fst = n[i]
          snd = if i < n.len-1: n[i+1] else: newEmptyNode()
        if fst.kind == nnkForStmt and snd.kind == nnkForStmt and
           fst.len == snd.len and fst[^2] == snd[^2] and # ^2 is loop range.
           safeLoopFusion(fst, snd):
          var forstmt = newNimNode(nnkForStmt)
          for j in 0..<fst.len-1:
            forstmt.add fst[j]
          var sndBody = snd[^1].copy
          for j in 0..<snd.len-2: # All loop variables.
            sndBody = sndBody.replace(snd[j], fst[j])
          var forBody = newStmtList()
          if fst[^1].kind in StmtNodes:
            for c in fst[^1]:
              forBody.add c.copy # Require this copy to avoid illegal storage access.
          else:
            forBody.add fst[^1]
          if sndBody.kind in StmtNodes:
            for c in sndBody:
              forBody.add c.copy # Require this copy to avoid illegal storage access.
          else:
            forBody.add sndBody
          for j in 0..<forBody.len: # Still need to make it recheck types.
            if forBody[j].kind in CallNodes:
              forBody[j] = forBody[j].callNodesWrap
          forstmt.add forBody.g
          result.add forstmt
          inc i, 2
        else:
          result.add fst.g
          if result[^1].kind in CallNodes: # Force type recheck.
            result[^1] = result[^1].copy
            result[^1] = result[^1].callNodesWrap
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
      if n[^1].kind in CallNodes: # Force type recheck.
        result.add n[^1].copy   # We don't change n.
        result[^1] = result[^1].callNodesWrap
      else:
        result.add n[^1].g
    else:
      result = n
    # echo "<<<< fusion:g => ", result.repr
  result = n.g
  # hint "<<<< fusion => " & result.treerepr
  dbg "fusion => ", result, TPLDebug.detail
template fusion(n: typed): stmt =
  fixpointcall(fusionHelper, n)
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
  cleanup:
    withDbgLevel TPLDebug(v):
      showCallResult:
        fusion cleanup looping autoSum requireTemporary splitting convertAutoDummy reAssign n
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
  var i = IndexType(v, 1).dummy
  result = "["
  if true:                    # This would put them in the same loops.
    result &= " " & $v[i]
    if i < hi1:
      result &= ","
  result &= " ]"
proc `$`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](m: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): string {.tensorOpsSilent.} =
  type
    I1 = IndexType(m, 1)
    I2 = IndexType(m, 2)
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
