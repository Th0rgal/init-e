import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.Assembly
import InitECandidate.Runtime.JournalSetSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem updateEq_update (locals : HolFiniteMapExact MlS (ValueHOL 64)) (name : MlS) (value : ValueHOL 64) :
    locals.updateEq (name,value) = locals.update (name,value) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq,HolFiniteMapExact.lookup_update,FUPDATE_HOL_eq_FUPDATE]

/-- An unused logical local preserves the actual source result and clock. -/
theorem evaluate_fresh_local_result_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ValueHOL 64) (program : ProgHOL 64)
    (fresh : name ∉ freeVarIdsHOL program) :
    (evaluateHOLFiniteState (setVarHOLFinite name value state) program).1 = (evaluateHOLFiniteState state program).1 ∧
    (evaluateHOLFiniteState (setVarHOLFinite name value state) program).2.clock = (evaluateHOLFiniteState state program).2.clock := by
  obtain ⟨locals,run,_⟩ := PanGlobalsFreshLocalAssembly.evaluateFreshLocalHOL name value program state
    (evaluateHOLFiniteState state program).1 (evaluateHOLFiniteState state program).2 ⟨fresh,rfl⟩
  have actual : evaluateHOLFiniteState (setVarHOLFinite name value state) program =
      ((evaluateHOLFiniteState state program).1,{(evaluateHOLFiniteState state program).2 with locals := locals}) := by
    simpa only [updateEq_update,setVarHOLFinite] using run
  rw [actual]
  exact ⟨rfl,rfl⟩

/-- The original journal-set source never references the logical rollback snapshot. -/
theorem jset_snapshot_fresh : ofString "snap" ∉ freeVarIdsHOL (sourceFunctionBody Guest.guestFn_jset) := by
  rw [source_journalSet32]
  simp [freeVarIdsHOL,varExpHOL,journalSetAfterGet32,journalSetCopy32,journalRecordSource32,journalSetFinish32]
  decide

#print axioms evaluate_fresh_local_result_clock
#print axioms jset_snapshot_fresh
end InitECandidate.Runtime
