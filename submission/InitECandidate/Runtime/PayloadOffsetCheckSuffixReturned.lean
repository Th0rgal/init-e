import InitECandidate.Runtime.PayloadOffsetCheckReturned
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned original payload suffix necessarily passed its four-offset
check; its continuation begins with the same memory and caller bindings. -/
theorem payload_offset_check_suffix_returned {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (offsets length : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 12) = (some (.returned value),post)) :
    state.memaddrs offsets ∧ memWord state.memory offsets = 540 ∧
      (∀ k : BitVec 64, k.toNat < 4 → SszOffsetOK state offsets 540 length k) ∧
      ∃ entry : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState state payloadOffsetCheckCall = (none,entry) ∧
        evaluateHOLFiniteState entry (payloadAt 13) = (some (.returned value),post) ∧
        entry.memory = state.memory ∧ entry.globals = state.globals ∧
        entry.memaddrs = state.memaddrs ∧ entry.locals = state.locals := by
  rw [source_payload_offset_check,evaluateHOLFiniteState_seq_line780] at run
  have noReturn := evaluate_discard_call_no_return state (ofString "ssz_check_offsets") payloadOffsetCheckArguments value
  change (evaluateHOLFiniteState state payloadOffsetCheckCall).1 ≠ some (.returned value) at noReturn
  cases checked : evaluateHOLFiniteState state payloadOffsetCheckCall with
  | mk result entry =>
    rw [checked] at run noReturn
    dsimp only at run noReturn
    cases result with
    | none =>
      obtain ⟨domain,first,all,memory,globals,addresses,locals⟩ :=
        payload_offset_check_returned state entry offsets length atOffsets atLength code checked
      exact ⟨domain,first,all,entry,rfl,run,memory,globals,addresses,locals⟩
    | some result =>
      have equal : some result = some (.returned value) := (Prod.mk.inj run).1
      exact False.elim (noReturn equal)

#print axioms payload_offset_check_suffix_returned
end InitECandidate.Runtime
