import macros
import debug,utils,seqset
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
macro fusionHelper(n: typed): untyped =
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
template fusion*(n: typed): untyped =
  fixpointcall(fusionHelper, n)
