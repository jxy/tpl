import macros

# Leave the following, which we generate using macros, commented out for reference.
#[
dumptree:
  type
    D1[V;lo1,hi1:static[int]] = object
      data: array[lo1..hi1,V]
    D2[V;lo1,hi1,lo2,hi2:static[int]] = object
      data: array[lo2..hi2,array[lo1..hi1,V]]

  template TensorDataDefault*(element: typedesc, lo1, hi1: int): expr =
    D1[element, lo1, hi1]
  template TensorDataDefault*(element: typedesc, lo1, hi1, lo2, hi2: int): expr =
    D2[element, lo1, hi1, lo2, hi2]

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
{.fatal: "".}
]#

proc genTensorData(n: int): NimNode {.compileTime.} =
  let
    tType = ident("TDD" & $n)
    E = newEmptyNode()
    V = ident"Element"
  const IxParam = ["lo", "hi"]
  # Generic Param: [V;loI,hiI,...:static[int]]
  var gParam = newNimNode(nnkGenericParams)
  gParam.add newNimNode(nnkIdentDefs).add(V, E, E)
  gParam.add newNimNode(nnkIdentDefs)
  for i in 1..n:
    for ix in IxParam:
      gParam[^1].add ident(ix & $i)
  gParam[^1].add(newNimNode(nnkStaticTy).add(ident"int"), E)
  # Full data type: TDDN[V,loI,hiI,...]
  var tTypeFull = newNimNode(nnkBracketExpr).add(tType, V)
  for i in 1..n:
    for ix in IxParam:
      tTypeFull.add ident(ix & $i)
  result = newStmtList()
  # Tensor type definition
  block:
    var Arr = V
    for i in 1..n:
      Arr = newNimNode(nnkBracketExpr).add(
        ident"array",
        infix(ident("lo" & $i), "..", ident("hi" & $i)),
        Arr)
    let objT = newNimNode(nnkObjectTy).add(
      E, E, newNimNode(nnkRecList).add(
        newNimNode(nnkIdentDefs).add(ident"data", Arr, E)))
    result.add newNimNode(nnkTypeSection).add newNimNode(nnkTypeDef).add(tType, gParam, objT)
  # Template to generate a Data type
  block:
    var
      fParam = newNimNode(nnkFormalParams).add(
        ident"expr",
        newNimNode(nnkIdentDefs).add(V, ident"typedesc", E),
        newNimNode(nnkIdentDefs))
      body = newStmtList().add(tTypeFull)
    for i in 1..n:
      for ix in IxParam:
        fParam[2].add ident(ix & $i)
    fParam[2].add(ident"int", E)
    result.add newNimNode(nnkTemplateDef).add(
      ident"TensorDataDefault".postfix "*", E, E, fParam, E, E, body)
  # Indexing procs
  block:
    let
      X = ident"x"
      Y = ident"y"
      procName = newNimNode(nnkAccQuoted).add(ident"[]").postfix "*"
    var
      fParam = newNimNode(nnkFormalParams).add(
        V, newNimNode(nnkIdentDefs).add(X, tTypeFull, E))
      body = X.newDotExpr ident"data"
    for i in 1..n:
      fParam.add newIdentDefs(ident("i" & $i), ident"int", E)
    for i in countdown(n,1):
      body = newNimNode(nnkBracketExpr).add(body, ident("i" & $i))
    let procIx = newNimNode(nnkProcDef).add(
      procName, E, gParam, fParam,
      newNimNode(nnkPragma).add(ident"inline"), E, newStmtList().add body)
    var procVIx = procIx.copy
    # [3] is FormalParams of a ProcDef
    procVIx[3][0] = newNimNode(nnkVarTy).add V # Return type.
    procVIx[3][1][1] = newNimNode(nnkVarTy).add tTypeFull # Type of X.
    var procIxEq = procVIx.copy
    procIxEq[0][1][0] = ident"[]=" # Proc name.
    procIxEq[3][0] = E
    procIxEq[3].add newIdentDefs(Y, V)
    procIxEq[6][0] = newAssignment(procIxEq[6][0], Y)
    result.add(procIx, procVIx, procIxEq)
macro genTensorDatas(n: static[int]): stmt =
  result = newStmtList()
  for i in 1..n:
    for c in genTensorData(i):
      result.add c
  # We `copy` complex structures to avoid some vm bugs.
  result = result.copy
const maxTensorDataRanks = 16
genTensorDatas(maxTensorDataRanks)
