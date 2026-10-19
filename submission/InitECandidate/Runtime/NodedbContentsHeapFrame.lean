import InitECandidate.Runtime.RunAttemptTwoDatabaseSlicesReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Fresh allocation and writes above an old heap preserve a constructed node
table, its witness membership, and the original readable bounded slice records. -/
theorem nodedb_contents_after_heap_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (post : PanSemStateFiniteExact 64 F)
    (table heap nextHeap array total input inputLength : BitVec 64)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ heap.toNat)
    (monotone : heap.toNat ≤ nextHeap.toNat)
    (domain : post.memaddrs = s.memaddrs) (endian : post.be = s.be) (code : post.code = s.code)
    (frame : ∀ address : BitVec 64, address.toNat < heap.toNat → post.memory address = s.memory address) :
    NodedbTableAt post table nextHeap total ∧
      HashTableValuesIn table (NodedbSliceTargets array total) post ∧
      RlpSliceInputPrefix post array input inputLength total.toNat := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,inv,ordered,extent⟩ := built
  have keep : ∀ address : BitVec 64, HtabFoot table capacity used order orderPos address.toNat →
      post.memory address = s.memory address := by
    intro address inside
    exact frame address (lt_of_lt_of_le (inv.foot_below address.toNat inside) extent)
  have cells := inv.toRegions.foot_keep (r := post) keep
  have invPost := inv.congr domain endian code cells.1 cells.2.1
  have orderedPost := ordered.congr inv.toRegions.count_le domain endian cells.2.1 cells.2.2.1 cells.2.2.2
  refine ⟨⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,invPost,
    orderedPost,le_trans extent monotone⟩,?_,?_⟩
  · apply entries.after_table_frame s post (NodedbSliceTargets array total) 32 table keys stride capacity used values
      order orderPos count bits inv domain endian
    intro address lower upper
    exact frame address (lt_of_lt_of_le upper extent)
  · apply RlpSliceInputPrefix.after_memory_between s post array total input inputLength heap 0 slices
      (Nat.zero_le _) arrayEnd domain
    intro address upper _
    exact frame address upper

#print axioms nodedb_contents_after_heap_frame
end InitECandidate.Runtime
