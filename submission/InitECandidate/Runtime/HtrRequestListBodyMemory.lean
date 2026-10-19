import InitECandidate.Runtime.HtrRequestListAllocationMemory
import InitECandidate.Runtime.HeapMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequestList_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk kind pointer size count heap out watched : BitVec 64) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (inputs : RequestListInputs state kind pointer size count out)
    (small : count.toNat ≤ 134217712) (budget : htrRequestListBodyCost count ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_request_list) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have enough : 1 ≤ state.clock := (Nat.le_add_right 1 _).trans budget
  obtain ⟨marked,_,clock,memory,globals,locals,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap layout.code layout.atHeap (by omega)
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (htrRequestListAt 0) = _ at run
  rw [source_htrRequestList_mark,declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
  change (let output := evaluateHOLFiniteState next (htrRequestListAt 1);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (htrRequestListAt 1) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have remaining : htrRequestListAllocationCost count ≤ next.clock := by
      change _ ≤ marked.clock
      change 1 + htrRequestListAllocationCost count ≤ state.clock at budget
      omega
    have nextInputs : RequestListInputs next kind pointer size count out :=
      ⟨(keep _ (by decide)).trans inputs.kindLocal,(keep _ (by decide)).trans inputs.pointerLocal,
        (keep _ (by decide)).trans inputs.sizeLocal,(keep _ (by decide)).trans inputs.countLocal,
        (keep _ (by decide)).trans inputs.outLocal⟩
    have frame := htrRequestList_allocation_returned_memory next inner sha accelerator zeroHashes chunk kind pointer size count heap out heap watched value
      (layout.transfer globals installed) nextInputs (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small remaining tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

#print axioms htrRequestList_body_returned_memory
end InitECandidate.Runtime
