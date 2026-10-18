import InitECandidate.Runtime.StatelessWitnessMiddleBound
import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.PanSeqAssoc
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessFirstWitnessStores : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "si"),.const 40]) (.rfield 0 (.var .local (ofString "st0"))))
    (.store (.op .add [.var .local (ofString "si"),.const 48]) (.rfield 1 (.var .local (ofString "st0"))))

theorem evaluate_stateless_first_stores_source {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (statelessAt 40) =
      evaluateHOLFiniteState state (.seq statelessFirstWitnessStores (statelessAt 42)) := by
  have source : statelessAt 40 =
      .seq (.store (.op .add [.var .local (ofString "si"),.const 40]) (.rfield 0 (.var .local (ofString "st0"))))
      (.seq (.store (.op .add [.var .local (ofString "si"),.const 48]) (.rfield 1 (.var .local (ofString "st0"))))
        (statelessAt 42)) := by
    simp only [statelessAt,statelessNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source,← evaluate_seq_assoc]
  rfl

/-- Recording the first witness list adds no clock to the checked bounds
for the middle and final witness lists; failed stores are covered. -/
theorem evaluate_stateless_first_witness_stores_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer first last length heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atFirst : state.locals.lookup (ofString "w1") = some (.val (.word first)))
    (atLast : state.locals.lookup (ofString "w2") = some (.val (.word last)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 40)
    state.clock ≤ evaluated.2.clock + (bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := clockPreserving_of_straightLine statelessFirstWitnessStores (by rfl) state
  have nt := evaluate_straightLine_no_timeout statelessFirstWitnessStores (by rfl) state
  have locals := fun key => evaluate_straight_local_frame key statelessFirstWitnessStores (by rfl) state
  have globals := evaluate_avoidsGlobalAssignment (ofString "heap_ptr") statelessFirstWitnessStores (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state statelessFirstWitnessStores
  rw [evaluate_stateless_first_stores_source,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state statelessFirstWitnessStores with
  | mk result middle =>
    rw [stored] at ticks nt locals globals metadata
    dsimp only at ticks nt locals globals metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,nt⟩
    | none =>
      dsimp only
      have tail := evaluate_stateless_middle_witness_bounded middle pointer first last length heapPointer
        ((locals _).trans atPointer) ((locals _).trans atFirst) ((locals _).trans atLast) ((locals _).trans atLength)
        (globals.trans heap) heapBound (metadata.1.trans code) (by rw [ticks]; exact budget)
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_stateless_first_witness_stores_bounded
end InitECandidate.Runtime
