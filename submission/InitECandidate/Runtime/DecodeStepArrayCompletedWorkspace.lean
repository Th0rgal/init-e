import InitECandidate.Runtime.DecodeStepListCompletedWorkspace
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_array_completed_workspace {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) (result : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 5) =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),result])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_decode_step_array] at run
  obtain ⟨value,output,evaluated,bodyRun,postEq⟩ := evaluate_dec_returned_scope s post (ofString "arr") .one
    (.rfield 0 (.var .local (ofString "sl"))) (decodeStepAt 6) _ run
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rfield 0 (.var .local (ofString "sl"))) = some (.val (.word array)) := by
    simp [evalHOLExact,atSlices]
  rw [evalArray] at evaluated
  cases evaluated
  let entered := setVarHOLFinite (ofString "arr") (.val (.word array)) s
  have enteredTable : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro index inside
    obtain ⟨p,n,entry⟩ := table index inside
    exact ⟨p,n,entry.after_frame _ _ _ _ _ _ _ _ rfl rfl rfl⟩
  have kept := decode_step_list_completed_workspace entered output array count input inputLength heap scratch frame
    ceiling inputLimit (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "sl" by decide] using atSlices)
    enteredTable inputBound limitCap atHeap heapBound aligned tableBefore arrayAbove scratchGlobal frameGlobal code ordered framePositive scratchBelow arena budget result bodyRun
  rw [postEq]
  exact kept
#print axioms decode_step_array_completed_workspace
end InitECandidate.Runtime
