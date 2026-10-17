import InitECandidate.Runtime.HashNewHeaderFailure
import InitECandidate.Runtime.CallNonreturnDestination
import InitECandidate.Runtime.OriginalHashNewCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A bounded nonreturning constructor body lifts to every handler-free call
destination, including failures after the variable-length occupancy clearing. -/
theorem evaluate_storage_table_bounded_failed_body_call {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS)) (steps : Nat)
    (code : state.code = originalRuntimeCode)
    (failure : let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
        (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32 : BitVec 64)))).update (ofString "cap",.val (.word (8 : BitVec 64)));
      let entry := callEntryStateHOLFinite state callee;
      let output := evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_new);
      output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧ entry.clock ≤ output.2.clock + steps ∧ output.2.clock ≤ entry.clock)
    (ticks : steps + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [.const 32,.const 8]);
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + (steps + 1) ∧ output.2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32 : BitVec 64)))).update (ofString "cap",.val (.word (8 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  let evaluated := evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_new)
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) (32 : BitVec 64) 8 (by decide) installed
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 32,.const 8] =
      some [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] := rfl
  have equal := evaluate_call_nonreturn_destination state evaluated.2 (ofString "htab_new") destination [.const 32,.const 8]
    [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1
    args lookup (by omega) rfl failure.2.2.1
  have terminal := evaluate_discard_call_body_terminal state evaluated.2 (ofString "htab_new") [.const 32,.const 8]
    [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1
    args lookup (by omega) rfl failure.2.2.1
  have noTimeout := evaluate_discard_call_body_no_timeout state evaluated.2 (ofString "htab_new") [.const 32,.const 8]
    [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1
    args lookup (by omega) rfl failure.2.1
  have clock := evaluate_discard_call_body_clock state evaluated.2 (ofString "htab_new") [.const 32,.const 8]
    [.val (.word (32 : BitVec 64)),.val (.word (8 : BitVec 64))] (sourceFunctionBody Guest.guestFn_htab_new) callee .one evaluated.1
    args lookup (by omega) rfl
  dsimp only
  rw [equal]
  refine ⟨terminal,noTimeout,?_,?_⟩
  · intro value
    exact evaluate_discard_call_no_return state (ofString "htab_new") [.const 32,.const 8] value
  · rw [clock]
    have cost := failure.2.2.2.1
    have remaining := failure.2.2.2.2
    change state.clock - 1 ≤ evaluated.2.clock + steps at cost
    change evaluated.2.clock ≤ state.clock - 1 at remaining
    exact ⟨by omega,by omega⟩

#print axioms evaluate_storage_table_bounded_failed_body_call
end InitECandidate.Runtime
