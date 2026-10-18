import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.SszFailCallTerminal
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadExtraDataGuard : ProgHOL 64 :=
  .ite (.cmp .lower (.const 32) (.op .sub [.var .local (ofString "o_txs"),.var .local (ofString "o_extra")]))
    (.call (some (none,none)) (ofString "ssz_fail") [.const 51]) .skip

theorem source_payload_extra_data_guard : payloadAt 13 = .seq payloadExtraDataGuard (payloadAt 14) := by
  simp only [payloadExtraDataGuard,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_payload_extra_data_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (extra transactions : BitVec 64)
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTransactions : state.locals.lookup (ofString "o_txs") = some (.val (.word transactions))) :
    evaluateHOLFiniteState state payloadExtraDataGuard =
      if (32 : BitVec 64) < transactions - extra then
        evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [.const 51])
      else (none,state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.const 32) (.op .sub [.var .local (ofString "o_txs"),.var .local (ofString "o_extra")])) =
      some (.val (.word (if (32 : BitVec 64) < transactions - extra then 1 else 0))) := by
    simp [evalHOLExact,evalListHOLExact,atExtra,atTransactions,wordOpHOL,wordOp,valueIsWord,valueWord,
      Compiler.Encoders.Asm.wordCmpHOL]
  unfold payloadExtraDataGuard
  rw [evaluateHOLFiniteState_ite,condition]
  by_cases oversized : (32 : BitVec 64) < transactions - extra
  · rw [if_pos oversized]
    simp
    intro smaller
    change 32 < (transactions - extra).toNat at oversized
    change (transactions - extra).toNat ≤ 32 at smaller
    omega
  · rw [if_neg oversized]
    simp [evaluateHOLFiniteState_skip]
    intro bigger
    exact False.elim (oversized bigger)

/-- Excess extra-data bytes reject before any following store or list call. -/
theorem evaluate_payload_extra_data_rejection_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (extra transactions : BitVec 64)
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTransactions : state.locals.lookup (ofString "o_txs") = some (.val (.word transactions)))
    (oversized : (32 : BitVec 64) < transactions - extra)
    (code : state.code = originalRuntimeCode) (nonzero : state.clock ≠ 0) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 13)
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have bounded := evaluate_sszFail_call_bounded state (.const 51) 51 code nonzero (by rfl)
  rw [source_payload_extra_data_guard,evaluateHOLFiniteState_seq_line780,
    evaluate_payload_extra_data_guard state extra transactions atExtra atTransactions,if_pos oversized]
  cases failed : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [.const 51]) with
  | mk result post =>
    rw [failed] at bounded
    dsimp only at bounded ⊢
    cases result with
    | none => exact False.elim (bounded.2.2 rfl)
    | some result =>
      dsimp only
      exact ⟨by have clock := bounded.1; omega,by have clock := bounded.1; omega,bounded.2.1,by simp⟩

/-- A returned suffix passed the extra-data guard and runs its following
stores from the exact same state; no positive clock assumption is needed. -/
theorem payload_extra_data_guard_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (extra transactions : BitVec 64) (value : ValueHOL 64)
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTransactions : state.locals.lookup (ofString "o_txs") = some (.val (.word transactions)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 13) = (some (.returned value),post)) :
    (transactions - extra).toNat ≤ 32 ∧
      evaluateHOLFiniteState state (payloadAt 14) = (some (.returned value),post) := by
  rw [source_payload_extra_data_guard,evaluateHOLFiniteState_seq_line780,
    evaluate_payload_extra_data_guard state extra transactions atExtra atTransactions] at run
  by_cases oversized : (32 : BitVec 64) < transactions - extra
  · rw [if_pos oversized] at run
    have terminal := evaluate_sszFail_call_terminal state (.const 51) 51 code (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "ssz_fail") [.const 51] value
    cases failed : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [.const 51]) with
    | mk result middle =>
      rw [failed] at run terminal noReturn
      dsimp only at run terminal noReturn
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
  · rw [if_neg oversized] at run
    change ¬ 32 < (transactions - extra).toNat at oversized
    exact ⟨by omega,run⟩

#print axioms evaluate_payload_extra_data_guard
#print axioms evaluate_payload_extra_data_rejection_bounded
#print axioms payload_extra_data_guard_returned
end InitECandidate.Runtime
