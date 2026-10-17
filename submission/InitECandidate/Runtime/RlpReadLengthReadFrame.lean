import InitECandidate.Runtime.RlpReadLengthBodyBound
import InitECandidate.Runtime.RlpReadLengthSyntax
import InitECandidate.Runtime.RlpFailReadFrame
import InitECandidate.Runtime.OriginalRlpReadLengthCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original length decoder preserves memory and globals at
all clocks, including failed header reads, canonicality errors and loop timeout. -/
theorem evaluate_rlpReadLength_body_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_read_length)).2.memory = state.memory ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_read_length)).2.globals = state.globals := by
  rw [source_rlpReadLength_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  cases condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) rlpReadLengthCheck with
  | none => exact ⟨rfl,rfl⟩
  | some value =>
    cases value with
    | rStruct fields => exact ⟨rfl,rfl⟩
    | nStruct name fields => exact ⟨rfl,rfl⟩
    | val value =>
      cases value with
      | word flag =>
        by_cases zero : flag = 0
        · simp only [if_pos zero,evaluateHOLFiniteState_skip]
          exact evaluate_rlpReadLength_after_check_frame state
        · simp only [if_neg zero]
          have first := evaluate_rlpFail_call_frame state (.const 2) 2 code (by rfl)
          cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 2]) with
          | mk result middle =>
            rw [run] at first
            dsimp only at first
            cases result with
            | none =>
              have next := evaluate_rlpReadLength_after_check_frame middle
              exact ⟨next.1.trans first.1,next.2.trans first.2⟩
            | some stopped => exact first

/-- The actual caller observes no memory or global changes from a length
read, including calls with insufficient clock or malformed input. -/
theorem evaluate_rlpReadLength_call_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_read_length") arguments)
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) pointer length (by decide) installed
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
  apply evaluate_discard_call_frame state (ofString "rlp_read_length") arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_read_length) callee .one args lookup
  intro result post run
  have frame := evaluate_rlpReadLength_body_frame (callEntryStateHOLFinite state callee) code
  rw [run] at frame
  exact frame

#print axioms evaluate_rlpReadLength_call_frame
#print axioms evaluate_rlpReadLength_body_frame
end InitECandidate.Runtime
