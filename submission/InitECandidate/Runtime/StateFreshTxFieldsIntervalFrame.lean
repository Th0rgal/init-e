import InitECandidate.Runtime.StateFreshTxFieldLoads
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Copying into an allocation after the transaction header preserves its
initialized table fields. The existing memcpy call contracts supply this frame. -/
theorem StateFreshTxFields.after_interval_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (ts fieldPointer destination size : BitVec 64)
    (fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (bounded : destination.toNat + size.toNat ≤ 33806089496)
    (afterHeader : ts.toNat + 72 ≤ destination.toNat)
    (frame : ∀ address : BitVec 64,
      address.toNat < destination.toNat ∨ destination.toNat + size.toNat ≤ address.toNat →
      post.memory address = state.memory address) :
    StateFreshTxFields ts fieldPointer stateFreshTxAllTables post := by
  intro binding member
  rcases binding with ⟨offset,table⟩
  have offsets := List.mem_map_of_mem (f := Prod.fst) member
  rw [stateFreshTx_table_binding_offsets] at offsets
  have small : offset < 72 := by simp at offsets; omega
  have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have address : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  have outside : (ts + BitVec.ofNat 64 offset).toNat < destination.toNat := by
    rw [address]
    omega
  exact (frame (ts + BitVec.ofNat 64 offset) (Or.inl outside)).trans (fields (offset,table) member)

#print axioms StateFreshTxFields.after_interval_frame
end InitECandidate.Runtime
