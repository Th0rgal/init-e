import InitECandidate.Runtime.HtrRequestsAllocationMemory
import InitECandidate.Runtime.HtrRequestsCallBound
import InitECandidate.Runtime.HeapMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrRequests_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap out watched : BitVec 64) (value : ValueHOL 64)
    (ctx : HtrRequestsEntryContext state sha accelerator zeroHashes chunk record heap out)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (budget : htrRequestsBodyCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_requests) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have enough : 1 ≤ state.clock := by unfold htrRequestsBodyCost at budget; omega
  obtain ⟨marked,_,clock,memory,globals,locals,installed,domain,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap layout.code layout.atHeap (by omega)
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrRequestsAt 0) = _ at run
  rw [source_htrRequests_mark,declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
  change (let output := evaluateHOLFiniteState next (htrRequestsAt 1);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (htrRequestsAt 1) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have nextCtx : HtrRequestsEntryContext next sha accelerator zeroHashes chunk record heap out :=
      ctx.after_frame keep globals memory domain installed
    have nextLayout : ListHashMemoryLayout next sha accelerator zeroHashes chunk heap out watched :=
      layout.transfer globals installed
    have remaining : htrRequestsAllocationCost ≤ next.clock := by
      change _ ≤ marked.clock
      unfold htrRequestsBodyCost at budget
      omega
    have frame := htrRequests_allocation_returned_memory next inner sha accelerator zeroHashes chunk record heap out heap watched value
      nextCtx nextLayout (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) remaining tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

/-- The installed requests-container hash preserves every word outside its
output and hash workspaces and below its fresh allocations. -/
theorem htrRequests_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (sha accelerator zeroHashes chunk record heap out watched : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word record),.val (.word out)])
    (budget : htrRequestsBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_requests") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have lookup := htrRequests_installed state record out workspace.code
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_requests")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_requests) _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "rq",.val (.word record))).update (ofString "out",.val (.word out)))
  have entryDecoded : HtrRequestsDecoded entry record := by
    intro index inside
    obtain ⟨p,n,old,small⟩ := decoded index inside
    exact ⟨p,n,old.after_frame state entry record index p n rfl rfl rfl,small⟩
  have ctx : HtrRequestsEntryContext entry sha accelerator zeroHashes chunk record heap out :=
    ⟨workspace.transfer rfl rfl,
      (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),
      (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),entryDecoded⟩
  rw [postEq]
  exact htrRequests_body_returned_memory entry output sha accelerator zeroHashes chunk record heap out watched value
    ctx (layout.transfer rfl rfl) (by change htrRequestsBodyCost ≤ state.clock - 1; omega) bodyRun

#print axioms htrRequests_body_returned_memory
#print axioms htrRequests_call_normal_memory
end InitECandidate.Runtime
