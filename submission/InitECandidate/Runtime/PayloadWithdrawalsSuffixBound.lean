import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.SszFixedListCountDeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadWithdrawalsCountArguments : List (ExpHOL 64) :=
  [.op .sub [.var .local (ofString "o_bal"),.var .local (ofString "o_wd")],.const 44,.const 9223372036854775807]

theorem source_payload_withdrawals_count : payloadAt 19 =
    .decCall (ofString "nwd") .one (ofString "ssz_fixed_list_count") payloadWithdrawalsCountArguments (payloadAt 20) := by
  simp only [payloadWithdrawalsCountArguments,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original withdrawal-count call and all remaining payload header stores
are bounded, including malformed list lengths and inaccessible-store errors. -/
theorem evaluate_payload_withdrawals_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (withdrawals balance : BitVec 64)
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode) (budget : 67 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 19)
    state.clock ≤ evaluated.2.clock + 67 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadWithdrawalsCountArguments =
      some [.val (.word (balance - withdrawals)),.val (.word (44 : BitVec 64)),.val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadWithdrawalsCountArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atWithdrawals,atBalance,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_withdrawals_count]
  exact evaluate_sszFixedListCount_declaration_bounded state (ofString "nwd") (payloadAt 20)
    payload_store_tail_straight payloadWithdrawalsCountArguments (balance - withdrawals) 44 9223372036854775807
    args code (by decide) budget

#print axioms evaluate_payload_withdrawals_suffix_bounded
end InitECandidate.Runtime
