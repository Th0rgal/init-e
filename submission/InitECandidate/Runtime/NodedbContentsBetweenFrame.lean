import InitECandidate.Runtime.NodedbContentsAboveFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A memory frame between scratch and the old heap preserves the exact
constructed DB metadata and original-input slice registry. -/
theorem nodedb_contents_after_between_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (table dbHeap array total input inputLength oldHeap : BitVec 64) (ceiling : Nat)
    (built : NodedbTableAt s table dbHeap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (tableEnd : dbHeap.toNat ≤ oldHeap.toNat)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ oldHeap.toNat)
    (domain : post.memaddrs = s.memaddrs) (endian : post.be = s.be) (code : post.code = s.code)
    (frame : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < oldHeap.toNat →
      post.memory address = s.memory address) :
    NodedbTableAt post table dbHeap total ∧
      HashTableValuesIn table (NodedbSliceTargets array total) post ∧
      RlpSliceInputPrefix post array input inputLength total.toNat := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,inv,ordered,extent⟩ := built
  have keep : ∀ address : BitVec 64, HtabFoot table capacity used order orderPos address.toNat →
      post.memory address = s.memory address := by
    intro address inside
    have upper := inv.foot_below address.toNat inside
    have := inv.headerKeys
    have := inv.keysBefore
    have := inv.usedBefore
    have := inv.orderBefore
    unfold HtabFoot at inside
    exact frame address (by omega) (by omega)
  have cells := inv.toRegions.foot_keep (r := post) keep
  refine ⟨⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,
    inv.congr domain endian code cells.1 cells.2.1,
    ordered.congr inv.toRegions.count_le domain endian cells.2.1 cells.2.2.1 cells.2.2.2,extent⟩,?_,?_⟩
  · apply entries.after_table_frame s post (NodedbSliceTargets array total) 32 table keys stride capacity used values
      order orderPos count bits inv domain endian
    intro address lower upper
    exact frame address (le_trans tableAbove lower) (by omega)
  · apply RlpSliceInputPrefix.after_memory_between s post array total input inputLength oldHeap ceiling slices
      arrayAbove arrayEnd domain
    intro address upper lower
    exact frame address lower upper

#print axioms nodedb_contents_after_between_frame
end InitECandidate.Runtime
