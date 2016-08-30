import macros,strutils
import debug,utils,seqdict,seqset,indexTypes
import XComplex
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
proc add(x: var replacePairs, fr, to: NimNode) =
  var
    p: rpair = (fr, to)
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
proc add(x: var replacePairs, p: rpair) =
  x.add(p.fr, p.to)
proc add(x: var replacePairs, ps: replacePairs) =
  for p in ps.data:
    x.add p
proc replace(n: NimNode, p: rpair): NimNode =
  n.replace(p.fr, p.to)
type
  Ixk = enum
    ixk0, ixkI, ixkE, ixkM, ixkT, ixkN
  ixtree = ref object
    case kind: Ixk
    of ixkI:
      vId, vIt: NimNode # dummy and its type
      con: bool         # if contracted via `*`; persistent
      ovId: NimNode     # Save the original assigned dummy
    of ixkE: vEl, vEr: ixtree  # lhs and rhs
    of ixkM:
      vM: seq[ixtree]           # operands of `*`
      nn: NimNode               # Identify this `*` op.
      scon: NimNode             # Special contraction expr to `*`.
    of ixkT: vT: seq[ixtree]   # indexing of a tensor
    of ixkN:
      vN: seq[ixtree]           # Other NimNode
      matched: replacePairs     # Matched indices of direct children
    of ixk0: discard           # Empty
proc treerepr(t: ixtree): string =
  case t.kind
  of ixk0:
    result = "--"
  of ixkI:
    result = "Ix " & t.vId.repr & "(was " & t.ovId.repr & ")" & ": " & t.vIt.repr & ", con: " & $t.con
  of ixkE:
    let
      lhs = t.vEl.treerepr.indent(2)
      rhs = t.vEr.treerepr.indent(2)
    result = "Eq\n" & lhs & "\n" & rhs
  of ixkM:
    result = "Mu: " & t.nn.lisprepr & "  scon: " & t.scon.repr
    for c in t.vM:
      result &= "\n" & c.treerepr.indent(2)
  of ixkT:
    result = "Ti"
    for c in t.vT:
      result &= "\n" & c.treerepr.indent(2)
  of ixkN:
    result = "Nn:"
    for c in t.matched:
      result &= " " & $c
    for c in t.vN:
      result &= "\n" & c.treerepr.indent(2)
proc `$`(t: ixtree): string = treerepr t
proc `$`(t: ptr ixtree): string = t.repr
proc contractAutoDummy(n: NimNode): NimNode =
  var dID {.compileTime global.} = 0
  proc newDummySym(n: NimNode): NimNode =
    result = nskVar.gensym "__D" & $dID & "__" & n.dummyStr
    inc dID
  let multWrap = ident"__TPL_internal_MultWrap__"
  var mID {.compileTime global.} = 0
  proc wrapMult(n: NimNode): NimNode =
    result = newCall(multWrap, mID.newlit, n)
    inc mID
  proc unwrapMult(n: NimNode, s: seqdict[NimNode, NimNode]): NimNode =
    if n.kind in CallNodes and n[0] == multWrap:
      let m = n[1]
      if m in s:
        result = newCall(ident"*", s[m], n[2].unwrapMult s).callNodesWrap
      else:
        result = n[2].unwrapMult s
    else:
      result = n
      for i in 0..<result.len:
        result[i] = result[i].unwrapMult s
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
      var i =
        if i.kind == ixkN and i.vN.len == 1:
          i.vN[0]
        else:
          i
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
  proc markContracted(t: var ixtree, s: NimNode, r = newEmptyNode()) =
    let r =                  # r is the replacement default to s.
      if r.kind == nnkEmpty: s else: r
    case t.kind
    of ixkI:
      if t.vId == s:
        t.vId = r
        t.con = true
    of ixkE:
      t.vEl.markContracted(s, r)
      t.vEr.markContracted(s, r)
    of ixkM:
      for i in 0..<t.vM.len:
        t.vM[i].markContracted(s, r)
    of ixkN:
      var matches: seqset[NimNode]
      matches.init
      matches.incl s
      for p in t.matched:
        if p.fr in matches:
          matches.incl p.to
        elif p.to in matches:
          matches.incl p.fr
      for i in 0..<t.vN.len:
        for x in matches:
          t.vN[i].markContracted(x, r)
    of ixkT:
      for i in 0..<t.vT.len:
        t.vT[i].markContracted(s, r)
    of ixk0:
      discard
  proc replaceAutoDummy(n: NimNode): (NimNode, ixtree) =
    # hint n.lisprepr
    if n.kind in CallNodes and $n[0] == "automaticIndex":
      var t = newPar()
      for i in 1..<n.len:
        t.add n[i]
      let d = t.newDummySym
      result = (d, ixtree(kind: ixkI, ovId: d, vId: d, vIt: t))
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
            ixtree(kind: ixkM, vM: @[], scon: newEmptyNode())
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
        if ixt.kind == ixkM:
          result = (nn.wrapMult, ixt)
          ixt.nn = result[0][1]
        else:
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
  type Ix = seqdict[NimNode, NimNode] # the symbol and its type
  proc collectDummy(t: ixtree): Ix =
    # Collect all ixkI kinds.
    result.init
    case t.kind
    of ixkI:
      result.add(t.vId, t.vIt)
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
  proc collectReplacement(t: ixtree): replacePairs =
    result.init
    case t.kind
    of ixkI:
      if t.ovId != t.vId:
        result.add(t.ovId, t.vId)
    of ixkE:
      result.add t.vEl.collectReplacement
      result.add t.vEr.collectReplacement
    of ixkM:
      for s in t.vM:
        result.add s.collectReplacement
    of ixkT:
      for s in t.vT:
        result.add s.collectReplacement
    of ixkN:
      for s in t.vN:
        result.add s.collectReplacement
      result.add t.matched
    of ixk0:
      discard
  proc collectSpecials(n: var seqdict[NimNode, NimNode], t: ixtree) =
    case t.kind
    of ixkE:
      n.collectSpecials t.vEl
      n.collectSpecials t.vEr
    of ixkM:
      for s in t.vM:
        n.collectSpecials s
      if t.scon.kind != nnkEmpty:
        n.add(t.nn, t.scon)
    of ixkT:
      for s in t.vT:
        n.collectSpecials s
    of ixkN:
      for s in t.vN:
        n.collectSpecials s
    else:
      discard
  proc rmReplaced(xs: Ix, ps: replacePairs): Ix =
    result.init
    for k, v in xs:
      var unReplaced = true
      for p in ps:
        if k == p.fr:
          unReplaced = false
          break
      if unReplaced:
        result.add(k, v)
  proc freeIx(t: ixtree, s: NimNode): seq[NimNode] =
    result = @[]
    case t.kind
    of ixkI:
      if t.vIt == s and not t.con:
        var newId = true
        for x in result:
          if x == t.vId:
            newId = false
            break
        if newId:
          result.add t.vId
    of ixkE:
      result.add t.vEl.freeIx s
      result.add t.vEr.freeIx s
    of ixkM:
      for c in t.vM:
        result.add c.freeIx s
    of ixkT:
      for c in t.vT:
        result.add c.freeIx s
    of ixkN:
      for c in t.vN:
        result.add c.freeIx s
      for p in t.matched:
        var
          frin = p.fr in result
          toin = p.to in result
        if frin and toin:
          result.delete p.fr
        elif frin:
          result.delete p.fr
        elif toin:
          result.delete p.to
    of ixk0:
      discard
  proc matchDummyType(t: var ixtree, s: NimNode) # Used in following recursions.
  proc contractMul(t: var ixtree, s: NimNode): int =
    # We contract nearby indices of tensors multiplied together.
    # hint "contractMul:t: " & t.treerepr
    # hint "contractMul:s: " & s.lisprepr
    case t.kind:
    of ixkM:
      var ixlist = newseq[seq[NimNode]](t.vM.len)
      for i in 0..<t.vM.len:
        result += t.vM[i].contractMul s
        ixlist[i] = t.vM[i].freeIx s
      if s[0].intval == TPL_complex:
        if ixlist.len >= 2 and ixlist[1].len > 0 and ixlist[0].len > 0:
          if t.vM.len != 2:
            warning t.treerepr
            error "Complex contraction only implemented for the dyadic multiplication."
          let
            o = newDummySym(s)
            lo = ixlist[0][^1]
            ro = ixlist[1][0]
          t.vM[0].markContracted lo
          t.vM[1].markContracted ro
          var m = ixtree(kind: ixkM, vM: @[], nn: newEmptyNode(), scon: newEmptyNode())
          m.add t.vM[0]
          m.add t.vM[1]
          t.vM[1] = m
          t.vM[0] = ixtree(kind: ixkT, vT: @[])
          t.vM[0].add ixtree(kind: ixkI, ovId:  o, vId:  o, vIt: s, con: false)
          t.vM[0].add ixtree(kind: ixkI, ovId: lo, vId: lo, vIt: s, con: true)
          t.vM[0].add ixtree(kind: ixkI, ovId: ro, vId: ro, vIt: s, con: true)
          t.scon = complexCoeff(o, lo, ro)
          # warning t.treerepr
        # Since we are not looping over multiple operands, we
        # don't need to change ixlist.
      else:
        for i in 1..<ixlist.len:
          if ixlist[i].len > 0:
            for prevI in countdown(i-1, 0):
              if ixlist[prevI].len > 0:
                t.vM[i].markContracted(ixlist[i][0], ixlist[prevI][^1])
                ixlist[i].del 0
                t.vM[prevI].markContracted ixlist[prevI][^1]
                ixlist[prevI].del(ixlist[prevI].len-1)
                break
    of ixkT:
      for i in 0..<t.vT.len:
        result += t.vT[i].contractMul s
      t.matchDummyType s
    of ixkN:
      for i in 0..<t.vN.len:
        result += t.vN[i].contractMul s
      t.matchDummyType s
    else:
      discard "Assumes nothing of interest for the rest."
    # hint "contractMul:t: " & t.treerepr
  proc match2(s: NimNode, lhs, rhs: var ixtree): (seq[NimNode], seq[NimNode]) =
    # Try to match lhs with rhs, returns replacement pairs and
    # non-contracted indices from lhs and rhs.
    # hint "match2: " & s.repr
    # hint "match2:BEGIN:lhs: " & lhs.treerepr
    # hint "match2:BEGIN:rhs: " & rhs.treerepr
    lhs.matchDummyType s
    rhs.matchDummyType s
    # hint "match2:AFTER matchDummyType:lhs: " & lhs.treerepr
    # hint "match2:AFTER matchDummyType:rhs: " & rhs.treerepr
    var
      lix = lhs.freeIx s
      rix = rhs.freeIx s
    # hint "match2:lix: " & $lix
    # hint "match2:rix: " & $rix
    while lix.len != rix.len:
      if lix.len > rix.len:
        let n = lhs.contractMul s
        lix = lhs.freeIx s
        if n == 0:
          break
      else:
        let n = rhs.contractMul s
        rix = rhs.freeIx s
        if n == 0:
          break
      # hint "match2:WHILE:lix: " & $lix
      # hint "match2:WHILE:rix: " & $rix
    result = (lix, rix)
  proc matchDummyType(t: var ixtree, s: NimNode) =
    # Make sure that indices of type `s` are matched.
    # hint ">>>> matchDummyType: " & s.repr
    # hint ">>>> matchDummyType <<<<\n" & t.treerepr
    case t.kind
    of ixkE:
      let (lix, rix) = s.match2(t.vEl, t.vEr)
      # hint "matchDummyType:lix " & lix.repr
      # hint "matchDummyType:rix " & rix.repr
      # hint "matchDummyType:rp " & rp.repr
      if lix.len != rix.len:
        # FIXME: what happens if len == 0?
        if lix.len <= 1 or rix.len <= 1: # Special Assignment Rule!
          let ix = if lix.len > 0: lix[0] else: rix[0]
          for c in lix:
            if c != ix:
              t.vEl.markContracted(c, ix)
          for c in rix:
            if c != ix:
              t.vEr.markContracted(c, ix)
        else:
          error "Cannot match dummy indices for type: " & s.repr
      else:
        for k in 0..<lix.len:
          t.vEl.markContracted lix[k]
          t.vEr.markContracted(rix[k], lix[k])
    of ixkN:
      let n = t.vn.len - 1
      # hint $n
      var
        changed = true
        unmatched = true
        idlen = newseq[int](n)
      while changed and unmatched:
        unmatched = false
        t.matched.init
        for i in 0..<n:
          # Matching nearby pairs of nodes
          # hint $i
          let
            olen = idlen[i]
            (lix, rix) = s.match2(t.vN[i], t.vN[i+1])
          if lix.len != rix.len:
            error "Cannot match dummy indices for type: " & s.repr
          for k in 0..<lix.len:
            t.matched.add((rix[k], lix[k]))
          idlen[i] = lix.len
          changed = changed or olen != idlen[i] # If any of the free index length changed.
        for i in 0..<n-1:
          if idlen[i] != idlen[i+1]:
            unmatched = true
            break
    of ixkM:
      for i in 0..<t.vM.len:
        t.vM[i].matchDummyType s
    of ixkT:
      for i in 0..<t.vT.len:
        t.vT[i].matchDummyType s
    else:
      discard "Nothing to worry about."
  proc matchDummy(t: var ixtree) =
    for s in t.alltypes:
      t.matchDummyType s
  # Stitch the functions together.
  var ixt: ixtree
  (result, ixt) = n.replaceAutoDummy
  if ixt.notempty:
    # hint "contractAutoDummy:n: " & n.repr
    # hint "contractAutoDummy:result: " & result.repr
    # hint "contractAutoDummy:ixt: " & ixt.treerepr
    ixt.matchDummy
    var specialContractions = newseqdict[NimNode, NimNode]()
    specialContractions.collectSpecials ixt
    result = result.unwrapMult specialContractions
    let reps = ixt.collectReplacement
    # hint "contractAutoDummy:reps: " & reps.repr
    for s in reps:
      result = result.replace s
    let ix = ixt.collectDummy.rmReplaced reps
    # hint "contractAutoDummy:ix: " & ix.repr
    result = newStmtList(
      newNimNode(nnkVarSection).add(
        newIdentDefs(gensym(nskVar, "__TPL__INTERNAL_REMOVE__"), newEmptyNode(), newLit(0))),
      result)
    for id, ty in ix:
      var d = newCall(bindsym"dummyIx")
      for s in ty:
        d.add s
      result[0].add newIdentDefs(id, newEmptyNode(), d)
    # hint "    --------------------"
    # hint "contractAutoDummy:result: " & result.repr
    # hint "contractAutoDummy:ixt: " & ixt.treerepr
macro convertAutoDummy*(n: typed): untyped =
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
