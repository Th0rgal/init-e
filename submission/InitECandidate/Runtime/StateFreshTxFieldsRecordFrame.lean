import InitECandidate.Runtime.StateFreshTxFieldLoads
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The transaction's eight table fields form two adjacent 32-byte blocks.
A memory frame for those blocks preserves the entire field invariant. -/
theorem StateFreshTxFields.after_two_record_frame {F : Type}
    {ts pointer : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (fields : StateFreshTxFields ts pointer stateFreshTxAllTables before)
    (frame : ∀ index : Nat, index < 2 → ∀ offset ∈ ([0,8,16,24] : List Nat),
      after.memory (ts + 8 + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (ts + 8 + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) :
    StateFreshTxFields ts pointer stateFreshTxAllTables after := by
  intro binding member
  rcases binding with ⟨offset,table⟩
  have offsets := List.mem_map_of_mem (f := Prod.fst) member
  rw [stateFreshTx_table_binding_offsets] at offsets
  have preserved : after.memory (ts + BitVec.ofNat 64 offset) = before.memory (ts + BitVec.ofNat 64 offset) := by
    simp at offsets
    rcases offsets with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [BitVec.add_assoc] using frame 0 (by decide) 0 (by simp)
    · simpa [BitVec.add_assoc] using frame 0 (by decide) 8 (by simp)
    · simpa [BitVec.add_assoc] using frame 0 (by decide) 16 (by simp)
    · simpa [BitVec.add_assoc] using frame 0 (by decide) 24 (by simp)
    · simpa [BitVec.add_assoc] using frame 1 (by decide) 0 (by simp)
    · simpa [BitVec.add_assoc] using frame 1 (by decide) 8 (by simp)
    · simpa [BitVec.add_assoc] using frame 1 (by decide) 16 (by simp)
    · simpa [BitVec.add_assoc] using frame 1 (by decide) 24 (by simp)
  exact preserved.trans (fields (offset,table) member)

#print axioms StateFreshTxFields.after_two_record_frame
end InitECandidate.Runtime
