import InitECandidate.Runtime.DiscardCallNoContinue
import InitECandidate.Runtime.StateRestoreRecordSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Source control flow that never emits a loop continue result. -/
def NoContinue {F : Type} (program : ProgHOL 64) : Prop :=
  ∀ state : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState state program).1 ≠ some .continue

theorem noContinue_dec {F : Type} (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (valid : NoContinue (F := F) body) : NoContinue (F := F) (.dec name shape initializer body) := by
  intro state
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split <;> try simp
  split
  · exact valid _
  · simp

theorem noContinue_ite {F : Type} (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (hy : NoContinue (F := F) yes) (hn : NoContinue (F := F) no) : NoContinue (F := F) (.ite condition yes no) := by
  intro state
  rw [evaluateHOLFiniteState_ite]
  split <;> try simp
  split
  · exact hn state
  · exact hy state

theorem noContinue_assign {F : Type} (kind : VarKind) (name : MlS) (value : ExpHOL 64) :
    NoContinue (F := F) (.assign kind name value) := by
  intro state
  rw [evaluateHOLFiniteState_assign]
  split <;> try simp
  split <;> simp

theorem noContinue_seq {F : Type} (first second : ProgHOL 64)
    (one : NoContinue (F := F) first) (two : NoContinue (F := F) second) :
    NoContinue (F := F) (.seq first second) := by
  intro state
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState state first]
  split
  · exact two _
  · exact one state

theorem stateRestore_record_no_continue {F : Type} : NoContinue (F := F) stateRestoreApplyRecord := by
  rw [stateRestore_apply_record_shape]
  apply noContinue_dec
  apply noContinue_dec
  apply noContinue_dec
  unfold stateRestoreRecordDecision
  apply noContinue_ite
  · intro state; exact evaluate_discard_call_no_continue state _ _
  · intro state; exact evaluate_discard_call_no_continue state _ _

theorem stateRestore_iteration_no_continue {F : Type} : NoContinue (F := F) stateRestoreLoopBody := by
  rw [stateRestore_loop_body_shape]
  exact noContinue_seq _ _ (noContinue_assign _ _ _) stateRestore_record_no_continue

#print axioms stateRestore_record_no_continue
#print axioms stateRestore_iteration_no_continue
end InitECandidate.Runtime
