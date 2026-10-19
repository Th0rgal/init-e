import InitECandidate.Runtime.HtrRequestListBodyMemory
import InitECandidate.Runtime.HtrRequestListCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normally returned request-list hashes preserve an earlier decoded metadata
cell outside the output and the SHA/length workspaces. No input-readability
or successful-allocation premise is imposed. -/
theorem htrRequestList_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes chunk kind pointer count size heap out watched : BitVec 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word kind),.val (.word pointer),.val (.word count),.val (.word size),.val (.word out)])
    (small : count.toNat ≤ 134217712) (budget : htrRequestListBodyCost count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_request_list") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have lookup := htrRequestList_installed state kind pointer count size out layout.code
  obtain ⟨returned,output,bodyRun,_,scope⟩ := evaluate_discardCall_normal_result state post (ofString "htr_request_list")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_request_list) _ args lookup run
  let entry := callEntryStateHOLFinite state (requestListParams kind pointer count size out)
  have inputs : RequestListInputs entry kind pointer size count out := by
    constructor <;> simp (config := {decide := true}) [entry,requestListParams,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [scope]
  exact htrRequestList_body_returned_memory entry output sha accelerator zeroHashes chunk kind pointer size count heap out watched returned
    (layout.transfer rfl rfl) inputs small (by change htrRequestListBodyCost count ≤ state.clock - 1; omega) bodyRun

#print axioms htrRequestList_call_normal_memory
end InitECandidate.Runtime
