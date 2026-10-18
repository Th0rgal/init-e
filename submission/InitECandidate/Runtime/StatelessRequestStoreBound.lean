import InitECandidate.Runtime.StatelessWitnessEntryBound
import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessRequestStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "si"),.const 32]) (.var .local (ofString "rq"))

theorem source_stateless_request_store : statelessAt 29 =
    .seq statelessRequestStore (statelessAt 30) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The request-result store preserves the witness input bound. A failed
store is an immediate termination and consumes no source clocks. -/
theorem evaluate_stateless_request_store_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (ordered : offset ≤ length) (budget : length.toNat + 23 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 29)
    state.clock ≤ evaluated.2.clock + (length.toNat + 23) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := clockPreserving_of_straightLine statelessRequestStore (by rfl) state
  have nt := evaluate_straightLine_no_timeout statelessRequestStore (by rfl) state
  have locals := fun key => evaluate_straight_local_frame key statelessRequestStore (by rfl) state
  have globals := fun key => evaluate_avoidsGlobalAssignment key statelessRequestStore (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state statelessRequestStore
  rw [source_stateless_request_store,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state statelessRequestStore with
  | mk result middle =>
    rw [stored] at ticks nt locals globals metadata
    dsimp only at ticks nt locals globals metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,nt⟩
    | none =>
      dsimp only
      have tail := evaluate_stateless_witness_entry_input_bounded middle pointer length offset offsets heapPointer
        ((locals _).trans atPointer) ((locals _).trans atLength) ((locals _).trans atOffset)
        ((globals _).trans atOffsets) ((globals _).trans heap) heapBound (metadata.1.trans code)
        ordered (by rw [ticks]; exact budget)
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_stateless_request_store_bounded
end InitECandidate.Runtime
