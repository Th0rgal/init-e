import InitECandidate.Runtime.StatelessWitnessMiddleStoresBound
import InitECandidate.Runtime.DecodeBytesListDeclarationContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessMiddleWitnessArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "wp"),.var .local (ofString "w1")],
    .op .sub [.var .local (ofString "w2"),.var .local (ofString "w1")],.const 9223372036854775807,.const 65536]

theorem source_stateless_middle_witness : statelessAt 42 =
    .decCall (ofString "cd") (.comb [.one,.one]) (ofString "decode_bytes_list")
      statelessMiddleWitnessArguments (statelessAt 43) := by
  simp only [statelessMiddleWitnessArguments,statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The middle and final witness-list declarations, header stores and return
compose with the sum of their two checked byte-list clock bounds. -/
theorem evaluate_stateless_middle_witness_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer first last length heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atFirst : state.locals.lookup (ofString "w1") = some (.val (.word first)))
    (atLast : state.locals.lookup (ofString "w2") = some (.val (.word last)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 42)
    state.clock ≤ evaluated.2.clock + (bytesListBound (last - first) + 1 + (bytesListBound (length - last) + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      statelessMiddleWitnessArguments = some [.val (.word (pointer + first)),.val (.word (last - first)),
        .val (.word (9223372036854775807 : BitVec 64)),.val (.word (65536 : BitVec 64))] := by
    simp [statelessMiddleWitnessArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atPointer,atFirst,atLast,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_stateless_middle_witness]
  apply evaluate_decodeBytesList_declaration_continuation_bounded state (ofString "cd") (statelessAt 43)
    (bytesListBound (length - last) + 1) statelessMiddleWitnessArguments (pointer + first) (last - first)
    9223372036854775807 65536 heapPointer args code heap heapBound budget
  intro value ready nextHeap locals installed domain nextGlobal nextBound other available
  have p : ready.locals.lookup (ofString "wp") = some (.val (.word pointer)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atPointer,show ofString "cd" ≠ ofString "wp" by decide]
  have w2 : ready.locals.lookup (ofString "w2") = some (.val (.word last)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atLast,show ofString "cd" ≠ ofString "w2" by decide]
  have len : ready.locals.lookup (ofString "wlen") = some (.val (.word length)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atLength,show ofString "cd" ≠ ofString "wlen" by decide]
  exact evaluate_stateless_middle_witness_stores_bounded ready pointer last length nextHeap p w2 len
    nextGlobal nextBound (installed.trans code) available

#print axioms evaluate_stateless_middle_witness_bounded
end InitECandidate.Runtime
