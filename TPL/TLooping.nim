import macros
import debug,utils,seqset,indexTypes
var forDummyId {.compileTime.} = 0
template forIndexCall[id,lo,hi:static[int]](s, f: expr, i: AnyIndex[TPLIndex.dummy,id,lo,hi], body: expr): untyped =
  for s in f(id, lo, hi):
    body
template forIndex[id,lo,hi:static[int]](s: expr, i: AnyIndex[TPLIndex.dummy,id,lo,hi], body: expr): untyped =
  for s in indices(id, lo, hi):
    body
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
macro looping*(n: typed): untyped =
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
