import InitECandidate.Runtime.TransactionSnapshot
import InitECandidate.Runtime.OriginalStateSnapshotCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

theorem source_stateSnapshot_body : sourceFunctionBody Guest.guestFn_state_snapshot =
    .return (.var .global (ofString "journal_n")) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

/-- The actual snapshot call reads the live journal count in one source clock;
its declaration form binds that count while preserving the transaction state. -/
theorem TransactionRuntimeWorld.snapshot_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (clock : state.clock ≠ 0) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_snapshot") []) = (none,post) ∧
      post.clock = state.clock - 1 ∧ TransactionRuntimeWorld widths fieldPointer ts journal snapshot count post ∧
      (∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "state_snapshot") [] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word count)) post) continuation;
            (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  let post := {state with clock := state.clock - 1}
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_state_snapshot) =
      (some (.returned (.val (.word count))),emptyLocalsHOLFinite entry) := by
    rw [source_stateSnapshot_body]
    have counter : entry.globals.lookup (ofString "journal_n") = some (.val (.word count)) := valid.journalWorld.world.counter
    simp [evaluateHOLFiniteState_return,evalHOLExact,counter,shapeOfHOLExact]
  have installed : state.code.lookup (ofString "state_snapshot") = some ([],sourceFunctionBody Guest.guestFn_state_snapshot,.one) := by
    rw [valid.journalWorld.code]; exact originalRuntimeCode_stateSnapshot_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "state_snapshot") (sourceFunctionBody Guest.guestFn_state_snapshot) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word count))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "state_snapshot") [] []
    (sourceFunctionBody Guest.guestFn_state_snapshot) HolFiniteMapExact.empty .one (.val (.word count)) (emptyLocalsHOLFinite entry)
    rfl lookup clock body shapeOk
  refine ⟨post,call,rfl,valid.after_read rfl rfl rfl rfl rfl,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state (emptyLocalsHOLFinite entry) name (ofString "state_snapshot") .one .one [] []
    (sourceFunctionBody Guest.guestFn_state_snapshot) continuation HolFiniteMapExact.empty (.val (.word count)) rfl lookup clock body
    (Nat.le_refl _) shapeOk shapeOk

#print axioms source_stateSnapshot_body
#print axioms TransactionRuntimeWorld.snapshot_call
end InitECandidate.Runtime
