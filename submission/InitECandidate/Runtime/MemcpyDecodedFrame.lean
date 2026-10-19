import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.RlpSliceRecordFrame
import InitECandidate.Runtime.RlpSliceInputPrefixFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A copy into a later allocation preserves a payload record field and the
complete decoded transaction slice table. Read failures need no extra domain premise. -/
theorem memcpy_call_normal_decoded_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (destination source size payload index pointer length array input inputLength : BitVec 64)
    (count : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word destination),.val (.word source),.val (.word size)])
    (entry : RlpSliceEntry state payload index pointer length) (indexBound : index.toNat ≤ 4)
    (slices : RlpSliceInputPrefix state array input inputLength count)
    (aligned : destination.toNat % 8 = 0) (fits : destination.toNat + size.toNat ≤ 33806089496)
    (recordBefore : payload.toNat + 72 < destination.toNat)
    (arrayBefore : array.toNat + count * 16 ≤ destination.toNat)
    (small : size.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : size.toNat / 32 + size.toNat / 8 + 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,post)) :
    RlpSliceEntry post payload index pointer length ∧ RlpSliceInputPrefix post array input inputLength count := by
  have frame (watched : BitVec 64) (before : watched.toNat < destination.toNat) :
      post.memory watched = state.memory watched := by
    have separate := memcpy_interval_separate destination size watched aligned fits (Or.inl before)
    exact memcpy_call_normal_memory state post arguments destination source size watched args code
      (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2) small budget run
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") arguments)
  rw [run] at metadata
  constructor
  · apply entry.after_record_frame state post payload index pointer length indexBound (by have := destination.isLt; omega) metadata.2.1
    intro watched lo hi
    exact frame watched (by omega)
  · apply slices.after_interval_frame state post array input inputLength count (by have := destination.isLt; omega) metadata.2.1
    intro watched lo hi
    exact frame watched (Nat.lt_of_lt_of_le hi arrayBefore)

#print axioms memcpy_call_normal_decoded_frame
end InitECandidate.Runtime
