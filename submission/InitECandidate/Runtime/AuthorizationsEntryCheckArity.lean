import InitECandidate.Runtime.AuthorizationsEntryCheckGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the actual arity guard implies precisely six fields. -/
theorem authorization_entry_check_normal_arity {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count : BitVec 64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (run : evaluateHOLFiniteState state authorizationEntryCheck = (none,final)) : count = 6#64 := by
  let guard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
    (.raise (ofString "TxErr") (.const 20)) .skip
  by_cases six : count = 6#64
  · exact six
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6)) = some (.val (.word 1)) := by
      simp [evalHOLExact,entryLocal,Compiler.Encoders.Asm.wordCmpHOL] <;> simp_all
    have failed : evaluateHOLFiniteState state guard =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 20)) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
        (.raise (ofString "TxErr") (.const 20)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 20)
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.const 20)
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.const 20) state
    rw [source_authorization_entry_check,evaluateHOLFiniteState_seq_line780,failed] at run
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 20)) with
    | mk result post =>
      rw [raised] at terminal safe clock run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        cases run

#print axioms authorization_entry_check_normal_arity
end InitECandidate.Runtime
