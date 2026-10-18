import InitECandidate.Runtime.StatelessPayloadStoreBound
import InitECandidate.Runtime.PayloadDeclarationContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessPayloadArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "np"),.var .local (ofString "o_pl")],
   .op .sub [.var .local (ofString "o_vh"),.var .local (ofString "o_pl")]]

theorem source_stateless_payload_call : statelessAt 22 =
    .decCall (ofString "pl") .one (ofString "decode_payload") statelessPayloadArguments
      (statelessAt 23) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete stateless decoder suffix from its payload call has an
input-length clock bound. Heap exhaustion is covered without assuming
capacity for a future allocation. -/
theorem evaluate_stateless_payload_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset np nlen rqOffset vhOffset payloadPointer payloadLength offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atNp : state.locals.lookup (ofString "np") = some (.val (.word np)))
    (atNlen : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (atRqOffset : state.locals.lookup (ofString "o_rq") = some (.val (.word rqOffset)))
    (atVhOffset : state.locals.lookup (ofString "o_vh") = some (.val (.word vhOffset)))
    (arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      statelessPayloadArguments = some [.val (.word payloadPointer),.val (.word payloadLength)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : payloadPointer.toNat + payloadLength.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ordered : offset ≤ length)
    (budget : sszSplitBound payloadLength + length.toNat + 525 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 22)
    state.clock ≤ evaluated.2.clock + (sszSplitBound payloadLength + length.toNat + 525) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_stateless_payload_call]
  have cost : sszSplitBound payloadLength + 80 + (length.toNat + 445) =
      sszSplitBound payloadLength + length.toNat + 525 := by omega
  rw [← cost]
  apply evaluate_payload_declaration_continuation_bounded state (ofString "pl") (statelessAt 23)
    (length.toNat + 445) statelessPayloadArguments payloadPointer payloadLength offsets heapPointer
    arguments atOffsets heap heapBound aligned scratchBelow inputFits domain0 domain8 domain16 domain24 heapArena
    code (by omega)
  intro value ready nextHeap locals installed domain nextGlobal nextBound other enough
  apply evaluate_stateless_payload_store_bounded ready pointer length offset np nlen rqOffset vhOffset offsets nextHeap
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ((other _ (by decide)).trans atOffsets) nextGlobal nextBound
    (installed.trans code) ordered enough
  all_goals rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,atPointer,atLength,atOffset,
    atNp,atNlen,atRqOffset,atVhOffset,
    show ofString "pl" ≠ ofString "p" by decide,
    show ofString "pl" ≠ ofString "len" by decide,
    show ofString "pl" ≠ ofString "o_wit" by decide,
    show ofString "pl" ≠ ofString "np" by decide,
    show ofString "pl" ≠ ofString "nlen" by decide,
    show ofString "pl" ≠ ofString "o_rq" by decide,
    show ofString "pl" ≠ ofString "o_vh" by decide]

#print axioms evaluate_stateless_payload_call_bounded
end InitECandidate.Runtime
