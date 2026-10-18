import InitECandidate.Runtime.PayloadWithdrawalsSuffixBound
import InitECandidate.Runtime.SszFixedListCountDeclarationReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned original payload withdrawal suffix has a whole number of
44-byte records, within the source's signed count limit. -/
theorem payload_withdrawals_suffix_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (withdrawals balance : BitVec 64) (value : ValueHOL 64)
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 19) = (some (.returned value),post)) :
    (balance - withdrawals) % 44 = 0 ∧ ((balance - withdrawals) / 44).toNat < 2^63 ∧
      ∃ (bodyPost output : PanSemStateFiniteExact 64 F), evaluateHOLFiniteState
        (setVarHOLFinite (ofString "nwd") (.val (.word ((balance - withdrawals) / 44))) {bodyPost with locals := state.locals})
        (payloadAt 20) = (some (.returned value),output) ∧
        post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadWithdrawalsCountArguments =
      some [.val (.word (balance - withdrawals)),.val (.word (44 : BitVec 64)),.val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadWithdrawalsCountArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atWithdrawals,atBalance,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_withdrawals_count] at run
  obtain ⟨divisible,within,rest⟩ := sszFixedListCount_declaration_returned state (ofString "nwd") (payloadAt 20)
    payloadWithdrawalsCountArguments (balance - withdrawals) 44 9223372036854775807 args code (by decide) post value run
  refine ⟨divisible,?_,rest⟩
  change ¬ 9223372036854775807 < ((balance - withdrawals) / 44).toNat at within
  omega

#print axioms payload_withdrawals_suffix_returned
end InitECandidate.Runtime
