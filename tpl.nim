import macros
import seqset
import utils
import tensor_data_default

####################
# index type
type
  gTindex[id,lo,hi:static[int]] = object {.requiresInit.}
    # `i` auto inits to 0, which is bad
    # `requiresInit` in v0.13 gives warning without an explicit initialization
    i: range[lo..hi]
converter idx2int*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): int = i.i
converter idx2float*[id,lo,hi:static[int]](i: gTindex[id,lo,hi]): float = i.i.float
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
template IndexType*(lo, hi: int): expr =
  type Index = gTindex[nextIndexID(),lo,hi]
  Index
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

template Dummy*[id,lo,hi:static[int]](t: typedesc[gTindex[id,lo,hi]]): expr =
  type Dummy = gTindexDummy[id,lo,hi]
  Dummy
template IndexType[id,lo,hi:static[int]](t: typedesc[gTindexDummy[id,lo,hi]]): expr =
  type Index = gTindex[id,lo,hi]
  Index
template IndexType[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): expr =
  t.type.IndexType
iterator items*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  type Index = IndexType(t)
  var i = Index(i: lo)
  while true:
    yield i
    if i.i == hi: break
    inc i.i
template head*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  IndexType(t)(i: lo)
iterator tail*[id,lo,hi:static[int]](t: gTindexDummy[id,lo,hi]): auto =
  type Index = IndexType(t)
  const lo1 = lo + 1
  if lo1 <= hi:
    var i = Index(i: lo1)
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
  index(IndexType(d), n)

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
const UniversalDummyIndex* = gTindexDummyU()
macro prepareDummy*(d: varargs[typed]): stmt =
  template convDummyU(cn, t: untyped): stmt =
    converter cn*(x: gTindexDummyU): t {.nodecl.} = discard
  result = newStmtList()
  for i in d:
    let
      id = newCall(bindsym"Dummy", i)
      conv = "__CONV_DummyU__2__" & i.dummyStr
    result.add getast(convDummyU(ident(conv), i))

####################
# tensor ops
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
    # if n.kind in CallNodes and n[0].kind == nnkClosedSymChoice:
    #   echo "  ### ", n[0].gettype.lisprepr
    #   for c in n[0]:
    #     echo "  ## ", c.lisprepr, " : ", c.gettype[1].lisprepr
    #     echo "  -> ", c.gettype[1].sametype gTindexDummy.gettype
    #     var s = newCall(c)
    #     for i in 1..<n.len:
    #       s.add n[i]
    #     echo s.gettype.lisprepr
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
    result = n[0]
  elif n.kind in CallNodes and $n[0] in autoSumFunctionNoBracket:
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
proc needAutoSum(n: NimNode, t: dummyTree): bool =
  let rhsLocalIx = t.idx - t.branch.getlhsix
  result = n.kind == nnkAsgn or (n.kind in CallNodes and $n[0].symbol in autoSumFunctions) and
    rhsLocalIx.len > 0

var dID {.global compiletime.} = 0
proc contractDummyU(n: NimNode): NimNode =
  # echo "\n>>>>  <= ", n.treerepr
  type
    ix = tuple
      sym: NimNode
      typ: NimNode
      con: bool
      outsider: bool
    ixlist = seq[ix]
  proc getOpenIx(n: ixlist): ixlist =
    result = newseq[ix]()
    for c in n:
      if not c.con:      # not contracted
        result.add c
  proc reversed(n: ixlist): ixlist =
    result = newseq[ix](n.len)
    for i in 0..<n.len:
      result[i] = n[n.len-1-i]
  proc pairContract(n: var ixlist): NimNode =
    result = newPar()
    for i, p in n:
      if p.con:                 # Skip contracted ones.
        continue
      for j in countdown(n.high, i+1):
        if n[j].con:            # Skip contracted ones.
          continue
        if p.typ == n[j].typ:   # same type
          result.add newPar(p.sym, n[j].sym)
          n[j].con = true
          break
  proc filterMissing(p: NimNode, n: ixlist): NimNode =
    # Receives and returns Par(Par(earlierSym, laterSym), ...)
    # Return pairs whose left one (earlierSym) is in n.
    result = newPar()
    for s in p:
      for i in n:
        if s[0] == i.sym:
          result.add s
          break          # Assumes each symbol only appears once.
  proc removeLeft(n: var ixlist, p: NimNode) =
    for s in p:
      for i in 0..<n.len:
        if s[0] == n[i].sym:
          n.del i
          break          # Assumes each symbol only appears once.
  proc uniqueIx(xs: varargs[ixlist]): ixlist =
    # echo "\n>>>> uniqueIx <="
    result = newseq[ix]()
    for x in xs:
      # echo "---- x ", x
      for i in x:
        var match = false
        for j in result:
          if i.sym == j.sym:
            match = true
            break
        if not match:
          result.add i
    # echo "<<<< uniqueIx => ", result
  proc replaceIx(n: NimNode, pair: NimNode): NimNode =
    result = n
    for p in pair:
      result = result.replace(p[0], p[1])
  proc g(previousDummy: var ixlist, n: NimNode): NimNode =
    if n.kind == nnkHiddenCallConv and
         $n.gettype == "gTindex" and
         $n[0].symbol.getimpl[3][1][1] == "gTindexDummyU": # sameType doesn't work.
      let t = n[0].symbol.getimpl[3][0] # The symbol of the return type of the converter.
      var i = previousDummy.len-1
      while i >= 0:
        if previousDummy[i].typ == t: # First same type ix from tail.
          break                 # Stop at the first same type always.
        dec i
      if i < 0 or not previousDummy[i].outsider:
        let d = gensym(nskVar, "__D" & $dID & "__" & $t)
        inc dID
        previousDummy.add((sym: d, typ: t, con: false, outsider: false))
        result = d
      else:         # Only contract with index from other tensor.
        previousDummy[i].con = true
        previousDummy[i].outsider = false
        result = previousDummy[i].sym
    else:
      if n.kind in CallNodes and $n[0] in ["[]", "[]="]:
        for i in 0..<previousDummy.len:
          # echo "set true"
          previousDummy[i].outsider = true
      result = n.safeCopyNimNode
      for i in n:
        result.add previousDummy.g i
      if result.kind in CallNodes:
        if $result[0] == "[]":
          var nbr = newNimNode(nnkBracketExpr)
          for i in 1..<result.len:
            nbr.add result[i]
          result = nbr
        # else:
        #   result[0] = ident($result[0]) # Force compiler to check the type again???
        # for i in 1..<result.len:
        #   if result[i].kind != nnkPar:
        #     result[i] = newPar(result[i])
        if result.kind != nnkPar:
          result = result.newPar
      elif result.kind == nnkHiddenDeref:
        result = result[0].newPar
      # elif result.kind in {nnkHiddenDeref, nnkHiddenAddr}:
      #   result = result[0].newPar
      # else:
      #   discard
    # echo "==== g => ", result.repr
    # echo "---- p => ", previousDummy
  result = n
  if n.kind == nnkAsgn or n.kind in CallNodes and $n[0] in autoSumFunctions:
    var rhsIxList = newseq[ix]()
    let rhs = rhsIxList.g n[^1]
    var lhsIxList = rhsIxList.getOpenIx.reversed # A list of ix that are not contracted at rhs.
    for i in 0..<lhsIxList.len:
      lhsIxList[i].outsider = true
    let
      lhs = lhsIxList.g n.getlhs # Uncontracted would left open after this.
      # pairContract: Extract those uncontracted pairs (earlier & later).
      # filterMissing: remove (earlier) ones that are not in rhsIxList away from the pairs.
      # So we never contract within lhs.
      pairContractRhsIx = lhsIxList.pairContract.filterMissing rhsIxList
    var requiredIx = uniqueIx(lhsIxList, rhsIxList)
    requiredIx.removeLeft pairContractRhsIx
    if requiredIx.len > 0:
      var ixDecl = newNimNode(nnkVarSection)
      for i in requiredIx:
        ixDecl.add newIdentDefs(i[0], newCall(bindsym"Dummy", ident($i[1])))
      if $n[0] in ["=", "[]="]:
        result = newAssignment(lhs, rhs.replaceIx pairContractRhsIx)
      else:
        result = infix(lhs, $n[0], rhs.replaceIx pairContractRhsIx)
      result = newStmtList().add(ixDecl, result)
  # echo "<<<< contractDummyU => ", result.treerepr
macro convertDummyU(n: typed): stmt =
  # echo "\n>>>> convertDummyU <= ", n.treerepr
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
  # echo "<<<< convertDummyU => ", result.treerepr

proc dummyLoopGen(ix: seqset[NimNode], n: NimNode): NimNode =
  proc reCall(n: NimNode): NimNode =
    # Look up symbol again to change a proc call to an iterator call.
    # FIXME: needs a more sophisticated treatment.
    result = n.copy # If we don't do copy, we will change n as well.
    if n.kind in CallNodes:
      result[0] = ident($n[0])
  result = n
  for i in ix:
    # echo i.repr, " : ", i.gettype.lisprepr
    # var ii = i.copy
    # if ii.kind in CallNodes: ii[0] = ident($ii[0])
    # hint "#### i: " & i.lisprepr
    let
      id = gensym(nskForVar, "__F__" & i.dummyStr)
      ii = i.reCall
    # hint "#### i: " & i.lisprepr
    var body = result.convert(i, id)
    # hint "**** dummyLoopGen:body => " & body.treerepr
    # if body.kind != nnkStmtList:
    #   body = newPar(body)
    result = newNimNode(nnkForStmt).add(id, ii, body)
macro splitLhsDuplicate(n: typed): stmt =
  # hint ">>>> splitLhsDuplicate <= " & n.treerepr
  # x[a,b] = y[b]
  #  -> x[a.head,b] = y[b]
  #     x[a.tail,b] = x[a.head,b]
  # echo ">>>> splitLhsduplicate: ", n.lisprepr
  # echo "     ", n.repr
  result = n                    # By default.
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      lhs = n.getlhs
      lhsIx = t.branch.getlhsix
      rhsIx = t.branch[^1].idx
      lhsLocalIx = t.idx - rhsIx
    # echo "lhs:        ", lhs.lisprepr
    # echo "lhsLocalIx: ", lhsLocalIx.repr
    if lhsLocalIx.len > 0:
      var
        stmtHead = n
        constHead = newNimNode(nnkConstSection)
        lhsTail = newseq[NimNode](lhsLocalIx.len)
      for m in 0..<lhsTail.len:
        lhsTail[m] = lhs
      for n, i in lhsLocalIx:
        let
          iheadCall = newCall(bindsym"head", i)
          ihead = gensym(nskConst, "__C__" & i.dummyStr)
          itail = newCall(bindsym"tail", i)
        constHead.add(newNimNode(nnkConstDef).add(ihead, newEmptyNode(), iheadCall))
        stmtHead = stmtHead.convert(i, ihead)
        for m in 0..<lhsTail.len:
          if m < n:
            lhsTail[m] = lhsTail[m].convert(i, ihead)
          elif m == n:
            lhsTail[m] = lhsTail[m].convert(i, itail)
          # Else, for m > n, do nothing.
      result = newStmtList().add(constHead, stmtHead)
      for c in lhsTail:
        result.add c.newAssignment stmtHead.getlhs
  # hint "<<<< splitLhsDuplicate => " & result.treerepr
macro splitRhsSum(n: typed): stmt =
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
      fun = $n[0]
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
          error "not implemented for lopLocalIx.len > 0"
        elif ropLocalIx.len > 0: # Similar to lopLocalIx.len > 0, but we honor order for "*" and "/".
          error "not implemented for ropLocalIx.len > 0"
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
  # echo "\n>>>> splitMultiOp <= ", n.repr
  result = n
  # echo "<<<< splitMultiOp => ", result.repr
proc accumulateAutoSum(n: NimNode): NimNode =
  # echo "\n>>>> accumulateAutoSum <= ", n.repr
  let t = n.genDummyTree
  if n.needAutoSum t:
    let
      fun = $n[0]
      lhs = n.getlhs
      rhs = n[^1]
      lhsIx = t.branch.getlhsix
      rhsLocalIx = t.idx - lhsIx
    if n.kind == nnkAsgn or fun == "[]=":
      var
        stmtHead = n
        constHead = newNimNode(nnkConstSection)
        accum = newseq[NimNode](rhsLocalIx.len)
      for m in 0..<accum.len:
        accum[m] = infix(lhs, "+=", rhs)
      for n, i in rhsLocalIx:
        let
          iheadCall = newCall(bindsym"head", i)
          ihead = gensym(nskConst, "__C__" & i.dummyStr)
          itail = newCall(bindsym"tail", i)
        constHead.add(newNimNode(nnkConstDef).add(ihead, newEmptyNode(), iheadCall))
        stmtHead = stmtHead.convert(i, ihead)
        for m in 0..<accum.len:
          if m < n:
            accum[m] = accum[m].convert(i, ihead)
          elif m == n:
            accum[m] = accum[m].convert(i, itail)
          # Else, for m > n, do nothing.
      result = newStmtList().add(constHead, stmtHead)
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
macro fusionHelper(n: typed): stmt =
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
          forstmt.add newStmtList().add(fst[^1], sndBody)
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
        result.add n[^1].copy
        if result[^1][1].kind != nnkPar:
          result[^1][1] = result[^1][1].newPar # Another ODD workaround for type mismatch.
      else:
        result.add n[^1]
    else:
      result = n
    # echo "<<<< fusion:g => ", result.repr
  result = n.g
  # hint "<<<< fusion => " & result.treerepr
template fusion(n: typed): stmt =
  fixpointcall(fusionHelper, n)
macro showResult(n: typed): stmt =
  result = n
  hint "tensorOps => " & n.repr
macro tensorOps*(n: untyped): stmt =
  template tensorOpsHelper(n: untyped): stmt =
    showResult fusion looping autoSum splitting convertDummyU n
  if n.kind in RoutineNodes:
    result = n
    result[6] = getast(tensorOpsHelper(n[6]))
  else:
    result = getast(tensorOpsHelper(n))

proc `$`*[D,V;id1,lo1,hi1:static[int]](v: gT1[D,V,id1,lo1,hi1]): string {.tensorOps.} =
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
proc `$`*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](m: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): string {.tensorOps.} =
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
