import InitECandidate.Runtime.DecodeStepListUniformBound
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual zero-clock array declaration is included in the list dispatch bound. -/
theorem runBounded_decode_step_array {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength heap scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitCap : inputLimit ≤ 134217712)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (tableBefore : array.toNat + count.toNat*16 ≤ heap.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) :
    RunBounded s (decodeStepAt 5) (decodeStepTwoCaseCost inputLimit) := by
  have reached := decode_step_array_reaches s array count atSlices
  have entryBudget : 0 + decodeStepTwoCaseCost inputLimit ≤ s.clock := by simpa using budget
  have bounded := RunBounded.ofReaches entryBudget reached (by
    intro next same ticks
    subst next
    let entered := setVarHOLFinite (ofString "arr") (.val (.word array)) s
    have enteredTable : RlpSliceInputPrefix entered array input inputLength count.toNat := by
      intro slot inside
      obtain ⟨p,n,entry⟩ := table slot inside
      exact ⟨p,n,entry.after_frame _ _ _ _ _ _ _ _ rfl rfl rfl⟩
    exact runBounded_decode_step_list_dispatch entered array count input inputLength heap scratch frame ceiling inputLimit
      (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "arr" ≠ ofString "sl" by decide] using atSlices)
      enteredTable inputBound limitCap atHeap heapBound aligned tableBefore arrayAbove scratchGlobal frameGlobal code ordered
      framePositive scratchBelow arena ticks)
  simpa using bounded

#print axioms runBounded_decode_step_array
end InitECandidate.Runtime
