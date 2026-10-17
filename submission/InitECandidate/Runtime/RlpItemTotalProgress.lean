import InitECandidate.Runtime.RlpItemTotalContinuation
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpItemTotal_return : rlpItemTotalReturn =
    .return (.op .add [.rfield 0 (.var .local (ofString "h")),.rfield 1 (.var .local (ofString "h"))]) := by
  simp only [rlpItemTotalReturn,rlpItemTotalContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A successful validation branch preserves the header local; no branch
can itself return an item size to bypass the final size computation. -/
theorem rlpItemTotal_validation_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header payload kind : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)])) :
    ((evaluateHOLFiniteState state rlpItemTotalValidation).1 = none →
      (evaluateHOLFiniteState state rlpItemTotalValidation).2.locals = state.locals) ∧
    (∀ value, (evaluateHOLFiniteState state rlpItemTotalValidation).1 ≠ some (.returned value)) := by
  rw [source_rlpItemTotal_validation,evaluateHOLFiniteState_ite]
  by_cases zero : kind = 0
  · subst kind
    have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    simp [evaluateHOLFiniteState_skip]
  · have notZero : kind ≠ 0#64 := zero
    have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,notZero,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    exact ⟨evaluate_discard_call_success_locals state _ _,evaluate_discard_call_no_return state _ _⟩

/-- Any returned item-total continuation value is exactly header plus payload,
even when the opaque validator can fail or mutate memory/globals. -/
theorem rlpItemTotal_continuation_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header payload kind : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]))
    (run : evaluateHOLFiniteState state rlpItemTotalContinuation = (some (.returned value),post)) :
    value = .val (.word (header + payload)) := by
  have scope := rlpItemTotal_validation_scope state header payload kind headerLocal
  rw [source_rlpItemTotal_continuation,evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state rlpItemTotalValidation with
  | mk result next =>
    rw [branchRun] at run scope
    cases result with
    | none =>
      have locals := scope.1 rfl
      have atHeader : next.locals.lookup (ofString "h") = some
          (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) := by
        rw [locals]; exact headerLocal
      have actual : evaluateHOLFiniteState next rlpItemTotalReturn =
          (some (.returned (.val (.word (header + payload)))),emptyLocalsHOLFinite next) := by
        rw [source_rlpItemTotal_return]
        simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atHeader,
          wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact]
      have equal := (Prod.mk.inj (run.symm.trans actual)).1
      exact PanSemResultExact.returned.inj (Option.some.inj equal)
    | some result =>
      have equal := (Prod.mk.inj run).1
      exact False.elim (scope.2 value equal)

/-- Successful item sizes are positive and input bounded, giving callers
strict progress for their own remaining-input measure. -/
theorem rlpItemTotal_continuation_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header payload kind length : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]))
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) length)
    (run : evaluateHOLFiniteState state rlpItemTotalContinuation = (some (.returned value),post)) :
    ∃ consumed : BitVec 64, value = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ length.toNat := by
  have fields := valid.fields header payload kind length
  exact ⟨header + payload,rlpItemTotal_continuation_returned state post header payload kind value headerLocal run,
    fields.2.2.2.1,fields.2.2.2.2.1⟩

#print axioms rlpItemTotal_continuation_returned
#print axioms rlpItemTotal_continuation_progress
end InitECandidate.Runtime
