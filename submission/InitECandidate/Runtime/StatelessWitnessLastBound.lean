import InitECandidate.Runtime.StatelessInputSource
import InitECandidate.Runtime.DecodeBytesListDeclarationStraightBound
import InitECandidate.Runtime.StoreChainReturnedLocal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessLastWitnessArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "wp"),.var .local (ofString "w2")],
    .op .sub [.var .local (ofString "wlen"),.var .local (ofString "w2")],.const 256,.const 1024]

theorem source_stateless_last_witness : statelessAt 45 =
    .decCall (ofString "hd") (.comb [.one,.one]) (ofString "decode_bytes_list")
      statelessLastWitnessArguments (statelessAt 46) := by
  simp only [statelessLastWitnessArguments,statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem stateless_final_stores_straight : straightLine (statelessAt 46) = true := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The final witness byte-list declaration and original stateless return
are bounded, including allocation, item-size rejection and failed stores. -/
theorem evaluate_stateless_last_witness_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer offset length heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atOffset : state.locals.lookup (ofString "w2") = some (.val (.word offset)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : bytesListBound (length - offset) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 45)
    state.clock ≤ evaluated.2.clock + (bytesListBound (length - offset) + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      statelessLastWitnessArguments = some [.val (.word (pointer + offset)),.val (.word (length - offset)),
        .val (.word (256 : BitVec 64)),.val (.word (1024 : BitVec 64))] := by
    simp [statelessLastWitnessArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atOffset,atLength,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_stateless_last_witness]
  exact evaluate_decodeBytesList_declaration_straight_bounded state (ofString "hd") (statelessAt 46)
    stateless_final_stores_straight statelessLastWitnessArguments (pointer + offset) (length - offset) 256 1024 heapPointer
    args code heap heapBound budget

/-- The final original stores return the unchanged stateless-input pointer. -/
theorem stateless_final_stores_returned_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "si") = some (.val (.word pointer)))
    (run : evaluateHOLFiniteState state (statelessAt 46) = (some (.returned value),post)) :
    value = .val (.word pointer) := by
  apply evaluate_storeChain_returned_local (key := ofString "si") ?_ state post pointer value atPointer run
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  change StoreChainReturnedLocal (ofString "si") (.seq (.store _ _) _)
  repeat first | apply StoreChainReturnedLocal.store | exact StoreChainReturnedLocal.finish

#print axioms source_stateless_last_witness
#print axioms evaluate_stateless_last_witness_bounded
#print axioms stateless_final_stores_returned_value
end InitECandidate.Runtime
