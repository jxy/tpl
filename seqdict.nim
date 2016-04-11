import macros

type
  seqdict*[K,V] = object
    keys: seq[K]
    values: seq[V]
proc newseqdict*[K,V]: seqdict[K,V] =
  result.keys.newseq(0)
  result.values.newseq(0)
proc init*[K,V](d: var seqdict[K,V]) =
  d.keys.newseq(0)
  d.values.newseq(0)
proc contains*[K,V](d: seqdict[K,V], k: K): bool =
  d.keys.contains k
iterator pairs*[K,V](d: seqdict[K,V]): (K,V) =
  let n = d.keys.len
  var i = 0
  while i != n:
    yield(d.keys[i], d.values[i])
    inc i
proc `[]`*[K,V](d: seqdict[K,V], k: K): V =
  var ix = -1
  for i, x in d.keys:
    if x == k:
      ix = i
      break
  if ix < 0:
    error "Nonexistent key, " & $k & ", in dict:\n" & d.repr
  result = d.values[ix]
proc `[]=`*[K,V](d: var seqdict[K,V], k: K, v: V) =
  var ix = -1
  for i, x in d.keys:
    if x == k:
      ix = i
      break
  if ix < 0:
    d.keys.add k
    d.values.add v
proc add*[K,V](d: var seqdict[K,V], k: K, v: V) =
  d[k] = v
proc add*[K,V](d: var seqdict[K,V], n: seqdict[K,V]) =
  for k, v in n:
    d[k] = v
