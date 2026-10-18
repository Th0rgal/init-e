import InitECandidate.Runtime.StatelessPayloadInputBound
import InitECandidate.Runtime.StatelessPayloadCallBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem evaluate_stateless_payload_input_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset np nlen plOffset rqOffset vhOffset offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atNp : state.locals.lookup (ofString "np") = some (.val (.word np)))
    (atNlen : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (atRqOffset : state.locals.lookup (ofString "o_rq") = some (.val (.word rqOffset)))
    (atVhOffset : state.locals.lookup (ofString "o_vh") = some (.val (.word vhOffset)))
    (atPlOffset : state.locals.lookup (ofString "o_pl") = some (.val (.word plOffset)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : np.toNat + nlen.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (heapArena : ∀ address : BitVec 64, address.toNat % 8 = 0 → heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ordered : offset ≤ length)
    (payloadOrdered : plOffset ≤ vhOffset) (hashOrdered : vhOffset ≤ nlen)
    (innerBound : nlen.toNat ≤ length.toNat)
    (budget : sszSplitBound length + length.toNat + 525 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 22)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + length.toNat + 525) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have plLe := BitVec.le_def.mp payloadOrdered
  have vhLe := BitVec.le_def.mp hashOrdered
  have span := BitVec.toNat_sub_of_le payloadOrdered
  have address : (np + plOffset).toNat = np.toNat + plOffset.toNat := by
    rw [BitVec.toNat_add]; omega
  have payloadFits : (np + plOffset).toNat + (vhOffset - plOffset).toNat < 2 ^ 64 := by
    rw [address,span]; omega
  have costLe : sszSplitBound (vhOffset - plOffset) ≤ sszSplitBound length := by
    unfold sszSplitBound
    rw [span]
    omega
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      statelessPayloadArguments = some [.val (.word (np + plOffset)),.val (.word (vhOffset - plOffset))] := by
    simp [statelessPayloadArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atNp,atPlOffset,atVhOffset,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  have bound := evaluate_stateless_payload_call_bounded_cells state pointer length offset np nlen rqOffset vhOffset
    (np + plOffset) (vhOffset - plOffset) offsets heapPointer atPointer atLength atOffset atNp atNlen atRqOffset
    atVhOffset arguments atOffsets heap heapBound aligned scratchBelow payloadFits domain0 domain8 domain16 domain24
    heapArena code ordered (by omega)
  exact ⟨by have consumed := bound.1; omega,bound.2⟩

#print axioms evaluate_stateless_payload_input_bounded_cells
end InitECandidate.Runtime
