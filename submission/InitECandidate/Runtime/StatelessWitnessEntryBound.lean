import InitECandidate.Runtime.StatelessWitnessBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem source_stateless_witness_pointer : statelessAt 30 =
    .dec (ofString "wp") .one (.op .add [.var .local (ofString "p"),.var .local (ofString "o_wit")])
      (statelessAt 31) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_length : statelessAt 31 =
    .dec (ofString "wlen") .one (.op .sub [.var .local (ofString "len"),.var .local (ofString "o_wit")])
      (statelessAt 32) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Computing the actual witness subspan adds no source clocks. The bound
uses its unsigned length; the ordered outer offsets imply the input bound. -/
theorem evaluate_stateless_witness_entry_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : (length - offset).toNat + 23 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 30)
    state.clock ≤ evaluated.2.clock + ((length - offset).toNat + 23) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let one := setVarHOLFinite (ofString "wp") (.val (.word (pointer + offset))) state
  let ready := setVarHOLFinite (ofString "wlen") (.val (.word (length - offset))) one
  have pointerEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local (ofString "p"),.var .local (ofString "o_wit")]) =
        some (.val (.word (pointer + offset))) := by
    simp [evalHOLExact,evalListHOLExact,atPointer,atOffset,wordOpHOL,wordOp,valueIsWord,valueWord]
  have lengthEval : @evalHOLExact 64 F _ one.toExact
      (fun a => Classical.propDecidable (one.memaddrs a))
      (.op .sub [.var .local (ofString "len"),.var .local (ofString "o_wit")]) =
        some (.val (.word (length - offset))) := by
    simp [one,setVarHOLFinite,evalHOLExact,evalListHOLExact,atLength,atOffset,
      HolFiniteMapExact.lookup_update,FUPDATE,wordOpHOL,wordOp,valueIsWord,valueWord,
      show ofString "wp" ≠ ofString "len" by decide,
      show ofString "wp" ≠ ofString "o_wit" by decide]
  rw [source_stateless_witness_pointer]
  apply evaluate_dec_word_post state (ofString "wp") _ _ (pointer + offset) _
    (fun r _ => r ≠ some .timeOut) (fun _ _ _ h => h) pointerEval
  rw [source_stateless_witness_length]
  apply evaluate_dec_word_post one (ofString "wlen") _ _ (length - offset) _
    (fun r _ => r ≠ some .timeOut) (fun _ _ _ h => h) lengthEval
  apply evaluate_stateless_witness_body_bounded ready (pointer + offset) (length - offset) offsets heapPointer
    ?_ ?_ atOffsets heap heapBound code budget
  all_goals simp [ready,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "wlen" ≠ ofString "wp" by decide]

theorem evaluate_stateless_witness_entry_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (ordered : offset ≤ length) (budget : length.toNat + 23 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 30)
    state.clock ≤ evaluated.2.clock + (length.toNat + 23) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have span := BitVec.toNat_sub_of_le ordered
  have bound := evaluate_stateless_witness_entry_bounded state pointer length offset offsets heapPointer
    atPointer atLength atOffset atOffsets heap heapBound code (by omega)
  exact ⟨by have consumed := bound.1; omega,bound.2⟩

#print axioms evaluate_stateless_witness_entry_bounded
#print axioms evaluate_stateless_witness_entry_input_bounded
end InitECandidate.Runtime
