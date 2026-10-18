import InitECandidate.Runtime.StatelessWitnessFirstStoresBound
import InitECandidate.Runtime.DecodeBytesListDeclarationContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessFirstWitnessArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "wp"),.var .local (ofString "w0")],
    .op .sub [.var .local (ofString "w1"),.var .local (ofString "w0")],.const 9223372036854775807,.const 1024]

theorem source_stateless_first_witness : statelessAt 39 =
    .decCall (ofString "st0") (.comb [.one,.one]) (ofString "decode_bytes_list")
      statelessFirstWitnessArguments (statelessAt 40) := by
  simp only [statelessFirstWitnessArguments,statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- All three original witness-list declarations, their stores and final
return compose with the sum of the three checked byte-list call bounds. -/
theorem evaluate_stateless_witness_lists_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer offset first last length heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atOffset : state.locals.lookup (ofString "w0") = some (.val (.word offset)))
    (atFirst : state.locals.lookup (ofString "w1") = some (.val (.word first)))
    (atLast : state.locals.lookup (ofString "w2") = some (.val (.word last)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : bytesListBound (first - offset) + 1 +
      (bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1)) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 39)
    state.clock ≤ evaluated.2.clock + (bytesListBound (first - offset) + 1 +
      (bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1))) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      statelessFirstWitnessArguments = some [.val (.word (pointer + offset)),.val (.word (first - offset)),
        .val (.word (9223372036854775807 : BitVec 64)),.val (.word (1024 : BitVec 64))] := by
    simp [statelessFirstWitnessArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atPointer,atOffset,atFirst,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_stateless_first_witness]
  apply evaluate_decodeBytesList_declaration_continuation_bounded state (ofString "st0") (statelessAt 40)
    (bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1))
    statelessFirstWitnessArguments (pointer + offset) (first - offset) 9223372036854775807 1024 heapPointer
    args code heap heapBound budget
  intro value ready nextHeap locals installed domain nextGlobal nextBound other available
  have p : ready.locals.lookup (ofString "wp") = some (.val (.word pointer)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atPointer,show ofString "st0" ≠ ofString "wp" by decide]
  have w1 : ready.locals.lookup (ofString "w1") = some (.val (.word first)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atFirst,show ofString "st0" ≠ ofString "w1" by decide]
  have w2 : ready.locals.lookup (ofString "w2") = some (.val (.word last)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atLast,show ofString "st0" ≠ ofString "w2" by decide]
  have len : ready.locals.lookup (ofString "wlen") = some (.val (.word length)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atLength,show ofString "st0" ≠ ofString "wlen" by decide]
  exact evaluate_stateless_first_witness_stores_bounded ready pointer first last length nextHeap p w1 w2 len
    nextGlobal nextBound (installed.trans code) available

/-- Ordered witness offsets make the total list-decoding cost linear in the
complete witness input length, without charging that length three times. -/
theorem stateless_witness_lists_cost_le (offset first last length : BitVec 64)
    (ordered0 : offset.toNat ≤ first.toNat) (ordered1 : first.toNat ≤ last.toNat)
    (ordered2 : last.toNat ≤ length.toNat) :
    bytesListBound (first - offset) + 1 +
      (bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1)) ≤ length.toNat + 12 := by
  have firstSpan := BitVec.toNat_sub_of_le (show offset ≤ first from ordered0)
  have middleSpan := BitVec.toNat_sub_of_le (show first ≤ last from ordered1)
  have lastSpan := BitVec.toNat_sub_of_le (show last ≤ length from ordered2)
  unfold bytesListBound sszSplitBound
  rw [firstSpan,middleSpan,lastSpan]
  omega

/-- The full original witness-list suffix uses at most witnessLength+12
source ticks once its offset checker has established ordered spans. -/
theorem evaluate_stateless_witness_lists_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer offset first last length heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atOffset : state.locals.lookup (ofString "w0") = some (.val (.word offset)))
    (atFirst : state.locals.lookup (ofString "w1") = some (.val (.word first)))
    (atLast : state.locals.lookup (ofString "w2") = some (.val (.word last)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (ordered0 : offset.toNat ≤ first.toNat) (ordered1 : first.toNat ≤ last.toNat)
    (ordered2 : last.toNat ≤ length.toNat) (budget : length.toNat + 12 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 39)
    state.clock ≤ evaluated.2.clock + (length.toNat + 12) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have cost := stateless_witness_lists_cost_le offset first last length ordered0 ordered1 ordered2
  have bounded := evaluate_stateless_witness_lists_bounded state pointer offset first last length heapPointer
    atPointer atOffset atFirst atLast atLength heap heapBound code (by omega)
  exact ⟨by have consumed := bounded.1; omega,bounded.2⟩

#print axioms evaluate_stateless_witness_lists_bounded
#print axioms stateless_witness_lists_cost_le
#print axioms evaluate_stateless_witness_lists_input_bounded
end InitECandidate.Runtime
