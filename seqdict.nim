import macros

type
  seqdict*[K,V] = object
    keys: seq[K]
    values: seq[V]
proc newseqdict*[K,V]: seqdict[K,V] =
  result.keys.newseq(0)
  result.values.newseq(0)
proc contains*[K,V](d: seqdict[K,V], k: K): bool =
  d.keys.contains k
proc `[]`*[K,V](d: seqdict[K,V], k: K): V =
  var ix = -1
  for i, x in d.keys:
    if x == k:
      ix = i
      break
  if ix < 0:
    error "Nonexistent key, " & $k & ", in dict:\n" & d.repr
  result = d.values[ix]
proc add*[K,V](d: var seqdict[K,V], k: K, v: V) =
  if k in d.keys:
    error "Key, " & $k & ", already exists in dict:\n" & d.repr
  d.keys.add k
  d.values.add v
