import macros
import strutils

const StmtNodes* = {nnkStmtList, nnkStmtListExpr}

iterator pairs*(n: NimNode): (int, NimNode) =
  for i in 0..<n.len:
    yield(i, n[i])
proc unwrap*(n: NimNode): NimNode =
  result = n
  while result.kind in {nnkPar, nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv}:
    result = if result.kind == nnkHiddenStdConv: result[1] else: result[0]

proc wrappedAssign*(lhs, rhs: NimNode): NimNode =
  if lhs.kind == nnkBracketExpr:
    for i in 0..<lhs.len:
      lhs[i] = lhs[i].newPar
  result = newAssignment(lhs, rhs.newPar)

proc rebindIndexing*(n: NimNode): NimNode =
  if $n[0] == "[]":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len:
      result.add n[i].unwrap.newPar
  elif $n[0] == "[]=":
    result = newNimNode(nnkBracketExpr)
    for i in 1..<n.len-1:
      result.add n[i].unwrap.newPar
    result = result.wrappedAssign n[^1]
  else:
    result = n

proc callNodesWrap*(n: NimNode): NimNode =
  # hint "callNodesWrap <= " & n.treerepr
  result = n
  if result[^1].kind == nnkHiddenStdConv:
    let nn = result[^1][1].copy
    if nn.kind == nnkBracket:   # A vararg
      result.del(result.len-1)
      for c in nn:
        if c.kind == nnkHiddenCallConv:
          result.add c[1]
        else:
          result.add c
    else:
      result[^1] = nn
  if result.len > 1:
    for i in 1..<result.len:
      if result[i].kind notin AtomicNodes + {nnkPar}:
        result[i] = unwrap(result[i]).newPar
  # hint "callNodesWrap => " & result.treerepr

proc replace*(n: NimNode, i: NimNode, j: NimNode): NimNode =
  # echo "\n>>>> replace"
  # echo n.lisprepr
  # echo i.lisprepr
  # echo j.lisprepr
  if n == i:
    result = j
  else:
    result = n.copyNimNode
    for c in n:
      result.add c.replace(i,j)
  # echo result.lisprepr
  # echo "<<<< replace"
proc convert*(n: NimNode, i: NimNode, j: NimNode): NimNode =
  # echo "\n>>>> convert"
  # echo n.treerepr
  # echo i.treerepr
  # echo j.treerepr
  proc go(n: NimNode, i: NimNode, j: NimNode): tuple[rep: bool, nn: NimNode] =
    # echo "  ==== go : ", n.lisprepr
    if n == i:
      # echo "  ---- n == i"
      result = (true, j)
    else:
      # echo "A"
      result.rep = false
      # echo "* n: ", n.lisprepr
      result.nn = n.copyNimNode
      # echo "THE node: ", result.nn.lisprepr
      # result.nn = n.copyNimNode # FIXME: we may not need the changes later if we stop using copyNimNode.
      # echo "THE node: ", result.nn.lisprepr
      for c in n:
        let cc = c.go(i,j)
        # echo "# ", cc.rep, " : ", cc.nn.lisprepr
        # echo "BEFORE"
        result.nn.add cc.nn
        # echo "AFTER"
        # echo "## ", result.rep, " : ", result.nn.lisprepr
        if cc.rep:
          result.rep = true
    #[
    if result.nn.kind == nnkHiddenAddr:
      # we may not need this, but just keep this kind here
      # just in case something breaks because of nnkHiddenAddr.
      result.nn = result.nn[0]
    ]#
    # The compiler wouldn't simply do the call conv again.
    # if result.nn.kind == nnkHiddenCallConv:
    #   # simply ask the compiler to do the call conv again
    #   result.nn = result.nn[1]
    # echo "## ", result.rep, " : ", result.nn.lisprepr
    if result.rep:
      if result.nn.kind == nnkHiddenCallConv:
        result.nn = result.nn[1]
      elif result.nn.kind in CallNodes:
        result.nn = result.nn.callNodesWrap.rebindIndexing
        # Make every sym ident would break generic function definitions.
        # result.nn[0] = ident($result.nn[0].symbol)
        # Limiting to indexing op only, may break with other replacment.
      # elif result.nn.kind in {nnkHiddenDeref, nnkHiddenAddr}:
      #   result.nn = if result.nn[0].kind == nnkPar: result.nn[0] else: result.nn[0].newPar
      elif result.nn.kind == nnkConv:
        # Deals with explicit converter, such as `int`, `float`.
        # echo result.nn.treerepr
        # result.nn[0] = ident($result.nn[0])
        var nnn = newCall(ident($result.nn[0].symbol))
        for i in 1..<result.nn.len:
          nnn.add result.nn[i]
        result.nn = nnn
    # echo "       repr : ", result.rep
    # echo "       node : ", result.nn.lisprepr
  result = go(n,i,j).nn
  # echo result.treerepr
  # echo "<<<< convert"
proc staticint*(x: NimNode): int =
  int(intVal(if x.kind == nnkSym: x.symbol.getImpl else: x))
macro unrollfor*(i: untyped, lo, hi: int, n: untyped): stmt =
  # echo "\n>>>> unrollfor"
  # echo n.treerepr
  result = newStmtList()
  let
    ll = staticint lo
    hh = staticint hi
  for j in ll..hh:
    result.add(n.replace(i, newLit(j)))
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< unrollfor"

proc dummyStr*(n: NimNode): string =
  let s = n.repr.strip
  var id = newString(s.len)
  var j = 0
  for i in 0..<s.len:
    if s[i] in IdentChars - {'_'}:
      id[j] = s[i]
      inc j
    elif j > 0 and id[j-1] != '_':
      id[j] = '_'
      inc j
  if id[j-1] == '_':
    dec j
  if j != s.len:
    id.setLen j
  return id
