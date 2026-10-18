import InitECandidate.Runtime.StatelessRequestCallBound
import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessHashStores : ProgHOL 64 :=
  .seq (.seq (.store (.op .add [.var .local (ofString "si"),.const 8])
      (.op .add [.var .local (ofString "np"),.var .local (ofString "o_vh")]))
    (.store (.op .add [.var .local (ofString "si"),.const 16]) (.var .local (ofString "nvh"))))
      (.store (.op .add [.var .local (ofString "si"),.const 24])
        (.op .add [.var .local (ofString "np"),.const 8]))

theorem evaluate_stateless_hash_stores_source {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (statelessAt 25) =
      evaluateHOLFiniteState state (.seq statelessHashStores (statelessAt 28)) := by
  have source : statelessAt 25 =
    .seq (.store (.op .add [.var .local (ofString "si"),.const 8])
      (.op .add [.var .local (ofString "np"),.var .local (ofString "o_vh")]))
    (.seq (.store (.op .add [.var .local (ofString "si"),.const 16]) (.var .local (ofString "nvh")))
      (.seq (.store (.op .add [.var .local (ofString "si"),.const 24])
        (.op .add [.var .local (ofString "np"),.const 8])) (statelessAt 28))) := by
    simp only [statelessAt,statelessNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source,← evaluate_seq_assoc,← evaluate_seq_assoc]
  rfl

/-- The three versioned-hash header stores add no clocks to the request
and witness bound, including inaccessible stores and malformed values. -/
theorem evaluate_stateless_hash_stores_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset np nlen rqOffset offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atNp : state.locals.lookup (ofString "np") = some (.val (.word np)))
    (atNlen : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (atRqOffset : state.locals.lookup (ofString "o_rq") = some (.val (.word rqOffset)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (ordered : offset ≤ length) (budget : length.toNat + 378 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 25)
    state.clock ≤ evaluated.2.clock + (length.toNat + 378) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := clockPreserving_of_straightLine statelessHashStores (by rfl) state
  have nt := evaluate_straightLine_no_timeout statelessHashStores (by rfl) state
  have locals := fun key => evaluate_straight_local_frame key statelessHashStores (by rfl) state
  have globals := fun key => evaluate_avoidsGlobalAssignment key statelessHashStores (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state statelessHashStores
  rw [evaluate_stateless_hash_stores_source,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state statelessHashStores with
  | mk result middle =>
    rw [stored] at ticks nt locals globals metadata
    dsimp only at ticks nt locals globals metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,nt⟩
    | none =>
      dsimp only
      have tail := evaluate_stateless_request_call_bounded middle pointer length offset (np + rqOffset) (nlen - rqOffset) offsets heapPointer
        ((locals _).trans atPointer) ((locals _).trans atLength) ((locals _).trans atOffset)
        (by simp [statelessRequestArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
          locals,atNp,atNlen,atRqOffset,wordOpHOL,wordOp,valueIsWord,valueWord])
        ((globals _).trans atOffsets) ((globals _).trans heap) heapBound (metadata.1.trans code)
        ordered (by rw [ticks]; exact budget)
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_stateless_hash_stores_bounded
end InitECandidate.Runtime
