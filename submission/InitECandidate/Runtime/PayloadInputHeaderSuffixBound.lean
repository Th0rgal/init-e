import InitECandidate.Runtime.PayloadOffsetReadsInputBound
import InitECandidate.Runtime.PayloadInputHeaderWrites
import InitECandidate.Runtime.StraightLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The initial input-header stores add no source ticks to the complete
remaining payload bound; inaccessible header-store failures are covered. -/
theorem evaluate_payload_input_header_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : sszSplitBound length + 78 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 2)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 78) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := clockPreserving_of_straightLine payloadInputHeader (by rfl) state
  have noTimeout := evaluate_straightLine_no_timeout payloadInputHeader (by rfl) state
  have locals := fun key => evaluate_straight_local_frame key payloadInputHeader (by rfl) state
  have globals := fun key => evaluate_avoidsGlobalAssignment key payloadInputHeader (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state payloadInputHeader
  have grouping : evaluateHOLFiniteState state (payloadAt 2) =
      evaluateHOLFiniteState state (.seq payloadInputHeader (payloadAt 4)) := by
    rw [source_payload_input_header,← evaluate_seq_assoc]
    rfl
  rw [grouping,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state payloadInputHeader with
  | mk result middle =>
    rw [stored] at ticks noTimeout locals globals metadata
    dsimp only at ticks noTimeout locals globals metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,noTimeout⟩
    | none =>
      dsimp only
      have tail := evaluate_payload_offset_reads_input_bounded middle pointer length offsets heapPointer
        ((locals _).trans atPointer) ((locals _).trans atLength) ((globals _).trans atOffsets)
        (metadata.1.trans code) ((globals _).trans heap) pointerBound
        (by rw [metadata.2.1]; exact domain0) (by rw [metadata.2.1]; exact domain8)
        (by rw [metadata.2.1]; exact domain16) (by rw [metadata.2.1]; exact domain24)
        (by rw [ticks]; exact budget)
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_payload_input_header_suffix_bounded
end InitECandidate.Runtime
