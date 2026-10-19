import InitECandidate.Runtime.NodedbContentsHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A scratch-only parser frame preserves the concrete constructed database,
its values registry and readable source-slice records in the upper arena. -/
theorem nodedb_contents_after_above_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (table heap array total input inputLength : BitVec 64) (ceiling : Nat)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ heap.toNat)
    (domain : post.memaddrs = s.memaddrs) (endian : post.be = s.be) (code : post.code = s.code)
    (frame : ∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = s.memory address) :
    NodedbTableAt post table heap total ∧
      HashTableValuesIn table (NodedbSliceTargets array total) post ∧
      RlpSliceInputPrefix post array input inputLength total.toNat := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,inv,ordered,extent⟩ := built
  have keep : ∀ address : BitVec 64, HtabFoot table capacity used order orderPos address.toNat →
      post.memory address = s.memory address := by
    intro address inside
    have := inv.headerKeys
    have := inv.keysBefore
    have := inv.usedBefore
    have := inv.orderBefore
    unfold HtabFoot at inside
    apply frame address
    omega
  have cells := inv.toRegions.foot_keep (r := post) keep
  refine ⟨⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,
    inv.congr domain endian code cells.1 cells.2.1,
    ordered.congr inv.toRegions.count_le domain endian cells.2.1 cells.2.2.1 cells.2.2.2,extent⟩,?_,?_⟩
  · apply entries.after_table_frame s post (NodedbSliceTargets array total) 32 table keys stride capacity used values
      order orderPos count bits inv domain endian
    intro address lower _
    exact frame address (le_trans tableAbove lower)
  · apply RlpSliceInputPrefix.after_memory_between s post array total input inputLength heap ceiling slices
      arrayAbove arrayEnd domain
    intro address _ above
    exact frame address above

#print axioms nodedb_contents_after_above_frame
end InitECandidate.Runtime
