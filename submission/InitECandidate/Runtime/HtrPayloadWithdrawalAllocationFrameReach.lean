import InitECandidate.Runtime.HtrPayloadWithdrawalAllocationSource
import InitECandidate.Runtime.AllocationAssignmentReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_withdrawal_allocation_frame_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array heap count chunks oldIndex : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word oldIndex)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : 2 ≤ state.clock) :
    Reaches state (htrPayloadAt 26)
      (fun next => HtrPayloadWithdrawalState array heap (allocationEnd heap (htrPayloadTxAllocationSize count)) count next count.toNat ∧
        next.locals.lookup (ofString "ch") = some (.val (.word chunks)) ∧
        next.code = originalRuntimeCode ∧
        (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat ≤ 33806089496 ∧
        next.memory = state.memory ∧ next.memaddrs = state.memaddrs ∧
        next.globals = (setGlobalHOLFinite (ofString "heap_ptr")
          (.val (.word (allocationEnd heap (htrPayloadTxAllocationSize count)))) state).globals ∧
        (∀ key, key ≠ ofString "roots" → key ≠ ofString "i" → next.locals.lookup key = state.locals.lookup key) ∧
        heap.toNat + (htrPayloadTxAllocationSize count).toNat ≤ (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat ∧
        (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat % 8 = 0)
      2 (htrPayloadAt 28) := by
  have allocated := evaluate_allocation_assignment_reaches state (ofString "roots") _ heap
    (htrPayloadTxAllocationSize count) (htrPayloadAt 27)
    (htrPayload_withdrawal_allocation_arguments state count countLocal) code heapGlobal heapBound budget
  rw [← source_htrPayload_withdrawal_allocation] at allocated
  exact reaches_trans state (htrPayloadAt 26) (htrPayloadAt 27) (htrPayloadAt 28)
    (AllocationDeclarationReady state (ofString "roots") heap (htrPayloadTxAllocationSize count))
    _ 2 0 allocated (by
      intro ready allocation
      have keep (key : MlS) (different : key ≠ ofString "roots") :
          ready.locals.lookup key = state.locals.lookup key := by
        rw [allocation.1]
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      let initialized := setVarHOLFinite (ofString "i") (.val (.word (0#64))) ready
      have assigned : evaluateHOLFiniteState ready (.assign .local (ofString "i") (.const 0)) =
          (none,initialized) := by
        have atIndex := (keep _ (by decide)).trans indexLocal
        simp [evaluateHOLFiniteState_assign,evalHOLExact,atIndex,lookupKvarHOLExact,isValidValueHOLExact,
          setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,initialized]
      rw [source_htrPayload_withdrawal_zero]
      apply reaches_seq
      left
      refine ⟨initialized,?_,by simp [initialized,setVarHOLFinite],by simp [initialized,setVarHOLFinite],assigned⟩
      refine ⟨?_,?_,allocation.2.2.1.trans code,allocation.2.2.2.2.2.1,allocation.2.1,allocation.2.2.2.1,allocation.2.2.2.2.1,?_,allocation.2.2.2.2.2.2.1,allocation.2.2.2.2.2.2.2⟩
      · refine { heapGlobal := ?_, arrayLocal := ?_, rootsLocal := ?_, countLocal := ?_, cursor := ?_ }
        · change ready.globals.lookup _ = _
          rw [allocation.2.2.2.2.1]
          simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            using (keep _ (by decide)).trans arrayLocal
        · simp (config := {decide := true}) [initialized,setVarHOLFinite,allocation.1,HolFiniteMapExact.lookup_update,FUPDATE]
        · simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            using (keep _ (by decide)).trans countLocal
        · exact ⟨0#64,by simp [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp⟩
      · simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
          using (keep _ (by decide)).trans chunksLocal
      · intro key notRoots notCounter
        change (ready.locals.update _).lookup key = _
        simpa [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notCounter] using keep key notRoots)

#print axioms htrPayload_withdrawal_allocation_frame_reaches
end InitECandidate.Runtime
