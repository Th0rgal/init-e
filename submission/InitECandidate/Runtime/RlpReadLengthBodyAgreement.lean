import InitECandidate.Runtime.RlpReadLengthAfterCheckAgreement
import InitECandidate.Runtime.RlpReadLengthBodyBound
import InitECandidate.Runtime.RlpFailCallTerminal
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful original length-reader body must pass its canonicality check;
its error call cannot return or complete normally to bypass that check. -/
theorem rlpReadLength_body_returned_after_check {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned value),post)) :
    evaluateHOLFiniteState state rlpReadLengthAfterCheck = (some (.returned value),post) := by
  rw [source_rlpReadLength_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
  cases condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) rlpReadLengthCheck with
  | none => rw [condition] at run; cases run
  | some flag =>
    rw [condition] at run
    cases flag with
    | rStruct fields => cases run
    | nStruct name fields => cases run
    | val flag =>
      cases flag with
      | word flag =>
        by_cases zero : flag = 0
        · simpa only [if_pos zero,evaluateHOLFiniteState_skip] using run
        · simp only [if_neg zero] at run
          have terminal := evaluate_rlpFail_call_terminal state (.const 2) 2 code (by rfl)
          have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 2] value
          cases failure : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 2]) with
          | mk result output =>
            rw [failure] at terminal noReturn run
            cases result with
            | none => exact False.elim (terminal rfl)
            | some stopped => exact False.elim (noReturn (Prod.mk.inj run).1)

/-- Complete original length-reader bodies returning successfully agree on
values from the same pointer/count and byte reads, despite unrelated state. -/
theorem rlpReadLength_body_returned_agreement {F : Type}
    (first second firstPost secondPost : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (firstValue secondValue : ValueHOL 64)
    (p1 : first.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n1 : first.locals.lookup (ofString "n") = some (.val (.word length)))
    (p2 : second.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n2 : second.locals.lookup (ofString "n") = some (.val (.word length)))
    (code1 : first.code = originalRuntimeCode) (code2 : second.code = originalRuntimeCode)
    (reads : ∀ address, @panMemLoadByteHOL 64 _ first.memory first.memaddrs
        (fun address => Classical.propDecidable (first.memaddrs address)) first.be address =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs
        (fun address => Classical.propDecidable (second.memaddrs address)) second.be address)
    (run1 : evaluateHOLFiniteState first (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned firstValue),firstPost))
    (run2 : evaluateHOLFiniteState second (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned secondValue),secondPost)) :
    firstValue = secondValue := by
  exact rlpReadLength_after_check_agreement first second firstPost secondPost pointer length firstValue secondValue p1 n1 p2 n2 reads
    (rlpReadLength_body_returned_after_check first firstPost firstValue code1 run1)
    (rlpReadLength_body_returned_after_check second secondPost secondValue code2 run2)

#print axioms rlpReadLength_body_returned_after_check
#print axioms rlpReadLength_body_returned_agreement
end InitECandidate.Runtime
