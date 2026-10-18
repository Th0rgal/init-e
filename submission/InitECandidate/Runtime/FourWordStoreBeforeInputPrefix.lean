import InitECandidate.Runtime.FourWordStoreInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A header store strictly before a slice array retains every readable input entry. -/
theorem fourWordStore_before_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address first second third fourth array count input inputLength : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
        some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : address.toNat + 24 < array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state (.store destination value)).2 array input inputLength count.toNat := by
  have n8 : (address + 8#64).toNat = address.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change address.toNat + 8 < 2^64; have h := array.isLt; omega)]
    rfl
  have n16 : (address + 16#64).toNat = address.toNat + 16 := by
    rw [BitVec.toNat_add_of_lt (by change address.toNat + 16 < 2^64; have h := array.isLt; omega)]
    rfl
  have n24 : (address + 24#64).toNat = address.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change address.toNat + 24 < 2^64; have h := array.isLt; omega)]
    rfl
  have memory : ∀ watched : BitVec 64, array.toNat ≤ watched.toNat →
      (evaluateHOLFiniteState state (.store destination value)).2.memory watched = state.memory watched := by
    intro watched above
    apply evaluate_fourWordStore_memory_frame state destination value address first second third fourth watched addressEval valueEval
    · intro equal; have same := congrArg BitVec.toNat equal; omega
    · intro equal; have same := congrArg BitVec.toNat equal; rw [n8] at same; omega
    · intro equal; have same := congrArg BitVec.toNat equal; rw [n16] at same; omega
    · intro equal; have same := congrArg BitVec.toNat equal; rw [n24] at same; omega
  have metadata := evaluateHOLFiniteState_metadata state (.store destination value)
  intro slot inside
  obtain ⟨pointer,length,item⟩ := valid slot inside
  have cell0 := rlpSlice_cell_toNat array slot count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  simp only [BitVec.add_zero,Nat.add_zero] at cell0
  exact ⟨pointer,length,item.after_frame state _ array slot pointer length input inputLength metadata.2.1
    (memory _ (by rw [cell0]; omega)) (memory _ (by rw [cell8]; omega))⟩

#print axioms fourWordStore_before_input_prefix
end InitECandidate.Runtime
