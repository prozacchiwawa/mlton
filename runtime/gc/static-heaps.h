/* Copyright (C) 2019 Matthew Fluet.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 */

#if (defined (MLTON_GC_INTERNAL_TYPES))

struct GC_staticHeap {
  pointer start;
  size_t size;
};

/*
 * Allowed references between heap objects:
 *
 * I -> {I,M,R}
 * M -> {I,M,R}
 * R -> {I,M,R,D}
 * D -> {I,M,R,D}
 */

struct GC_staticHeaps {
  struct GC_staticHeap immutable;
  struct GC_staticHeap mutable;
  struct GC_staticHeap root;
};

#endif /* (defined (MLTON_GC_INTERNAL_TYPES)) */

#if (defined (MLTON_GC_INTERNAL_FUNCS))

static inline bool isObjptrInImmutableStaticHeap (GC_state s, objptr op);
static inline bool isObjptrInMutableStaticHeap (GC_state s, objptr op);
static inline bool isObjptrInRootStaticHeap (GC_state s, objptr op);
static inline bool isObjptrInStaticHeap (GC_state s, objptr op);
static inline bool isPointerInImmutableStaticHeap (GC_state s, pointer p);
static inline bool isPointerInMutableStaticHeap (GC_state s, pointer p);
static inline bool isPointerInRootStaticHeap (GC_state s, pointer p);
static inline bool isPointerInStaticHeap (GC_state s, pointer p);

#endif /* (defined (MLTON_GC_INTERNAL_FUNCS)) */
