import InitECandidate.Runtime.StatelessWitnessLoadsBound
import InitECandidate.Runtime.StatelessWitnessOffsetBounds
import InitECandidate.Runtime.SszCheckOffsetsCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessWitnessCheckArguments : List (ExpHOL 64) :=
  [.var .global (ofString "ssz_offs"),.const 3,.const 12,.var .local (ofString "wlen")]

def statelessWitnessCheckCall : ProgHOL 64 :=
  .call (some (none,none)) (ofString "ssz_check_offsets") statelessWitnessCheckArguments

theorem source_stateless_witness_check : statelessAt 35 =
    .seq statelessWitnessCheckCall (statelessAt 36) := by
  simp only [statelessWitnessCheckCall,statelessWitnessCheckArguments,statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual witness offset check and complete remaining witness decoder
use at most witnessLength+20 clocks, including invalid-offset rejection. -/
theorem evaluate_stateless_witness_check_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : length.toNat + 20 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 35)
    state.clock ≤ evaluated.2.clock + (length.toNat + 20) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      statelessWitnessCheckArguments = some [.val (.word offsets),.val (.word (3 : BitVec 64)),
        .val (.word (12 : BitVec 64)),.val (.word length)] := by
    simp [statelessWitnessCheckArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atOffsets,atLength]
  have callBound := evaluate_sszCheckOffsets_call_bounded state none statelessWitnessCheckArguments offsets 3 12 length
    args code (by decide) (by change 8 ≤ state.clock; omega)
  change state.clock ≤ (evaluateHOLFiniteState state statelessWitnessCheckCall).2.clock + 8 ∧
    (evaluateHOLFiniteState state statelessWitnessCheckCall).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state statelessWitnessCheckCall).1 ≠ some .timeOut at callBound
  have metadata := evaluateHOLFiniteState_metadata state statelessWitnessCheckCall
  rw [source_stateless_witness_check,evaluateHOLFiniteState_seq_line780]
  cases checked : evaluateHOLFiniteState state statelessWitnessCheckCall with
  | mk result middle =>
    rw [checked] at callBound metadata
    dsimp only at callBound metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by have consumed := callBound.1; omega,callBound.2.1,callBound.2.2⟩
    | none =>
      dsimp only
      obtain ⟨contract,memory,globals,domain,locals⟩ := sszCheckOffsets_call_returned state
        statelessWitnessCheckArguments offsets 3 12 length args code (by decide) middle checked
      obtain ⟨_,accepted,first⟩ := contract
      have firstValue := (first (by decide)).2
      have d0 := (accepted 0 (by decide)).1
      change state.memaddrs (offsets + (0#64)) at d0
      rw [BitVec.add_zero] at d0
      have d8 : state.memaddrs (offsets + 8) := (accepted 1 (by decide)).1
      have d16 : state.memaddrs (offsets + 16) := (accepted 2 (by decide)).1
      obtain ⟨firstEqual,lower,ordered,upper⟩ := stateless_witness_offset_bounds state offsets length
        (memWord state.memory offsets) (memWord state.memory (offsets + 8)) (memWord state.memory (offsets + 16))
        firstValue accepted rfl rfl rfl
      have firstOrdered : (memWord state.memory offsets).toNat ≤ (memWord state.memory (offsets + 8)).toNat := by
        rw [firstEqual]; exact lower
      have tail := evaluate_stateless_witness_loads_bounded middle pointer length offsets
        (memWord state.memory offsets) (memWord state.memory (offsets + 8)) (memWord state.memory (offsets + 16))
        heapPointer (by rw [locals]; exact atPointer) (by rw [locals]; exact atLength)
        (by rw [globals]; exact atOffsets) (by rw [globals]; exact heap) heapBound (metadata.1.trans code)
        (by rw [domain]; exact d0) (by rw [domain]; exact d8) (by rw [domain]; exact d16)
        (by rw [memory]) (by rw [memory]) (by rw [memory]) firstOrdered ordered upper
        (by have consumed := callBound.1; omega)
      exact ⟨by have consumed := callBound.1; have after := tail.1; omega,
        by have remaining := callBound.2.1; have after := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_stateless_witness_check_bounded
end InitECandidate.Runtime
