import macros
import tensor_data_default,indexTypes

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
  template addIxParams(n: NimNode, i: int): untyped =
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
    result.add newNimNode(nnkTypeSection).add newNimNode(nnkTypeDef).add(
      newNimNode(nnkPostfix).add(ident"*", tType), gParam, objT)
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
macro genTensors(n: static[int]): untyped =
  result = newStmtList()
  for i in 1..n:
    for c in genTensor(i):
      result.add c
  # We `copy` complex structures to avoid some vm bugs.
  result = result.copy
  # echo "genTensors(", n, ") =>\n", result.repr
const maxTensorRanks* = 16
genTensors(maxTensorRanks)

proc addDot(d: var NimNode, i: NimNode, id: varargs[string]) =
  for s in id:
    d.add(i.newDotExpr s.ident)

proc genTensorType(container, element, index: NimNode): NimNode =
  result = newCall(bindsym"tensorType", container, element)
  for i in index:
    result.add i
  # echo "<<<< genTensortype => ", result.lisprepr
macro Tensor*(index: openarray[untyped], element, container: untyped): untyped =
  result = genTensorType(container, element, index)
macro Tensor*(index: openarray[untyped], element: untyped): untyped =
  var container = newCall(bindsym"TensorDataDefault", element)
  for i in index:
    container.addDot(i, "lo", "hi")
  result = genTensorType(container, element, index)
