import InitECandidate.Runtime.HtrU64AtMemoryFrame
import InitECandidate.Runtime.RlpSliceRecordFrame
import InitECandidate.Runtime.RlpSliceInputPrefixFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An integer hash into a later allocation preserves a payload record field and the
complete decoded transaction slice table. Read failures need no extra domain premise. -/
theorem htrU64At_call_normal_decoded_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (destination source payload index pointer length array input inputLength : BitVec 64)
    (count : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word source),.val (.word destination)])
    (entry : RlpSliceEntry state payload index pointer length) (indexBound : index.toNat ≤ 4)
    (slices : RlpSliceInputPrefix state array input inputLength count)
    (aligned : destination.toNat % 8 = 0) (fits : destination.toNat + 32 ≤ 33806089496)
    (recordBefore : payload.toNat + 72 < destination.toNat)
    (arrayBefore : array.toNat + count * 16 ≤ destination.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : 30 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_u64_at") arguments) = (none,post)) :
    RlpSliceEntry post payload index pointer length ∧ RlpSliceInputPrefix post array input inputLength count := by
  have frame (watched : BitVec 64) (before : watched.toNat < destination.toNat) :
      post.memory watched = state.memory watched := by
    exact htrU64At_call_normal_memory state post arguments source destination watched args code aligned fits
      (Or.inl before) budget run
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_u64_at") arguments)
  rw [run] at metadata
  constructor
  · apply entry.after_record_frame state post payload index pointer length indexBound (by have := destination.isLt; omega) metadata.2.1
    intro watched lo hi
    exact frame watched (by omega)
  · apply slices.after_interval_frame state post array input inputLength count (by have := destination.isLt; omega) metadata.2.1
    intro watched lo hi
    exact frame watched (Nat.lt_of_lt_of_le hi arrayBefore)

#print axioms htrU64At_call_normal_decoded_frame
end InitECandidate.Runtime
