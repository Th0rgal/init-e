import InitECandidate.Runtime.StatelessRequestStoreBound
import InitECandidate.Runtime.DecodeRequestsDeclarationContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessRequestArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "np"),.var .local (ofString "o_rq")],
   .op .sub [.var .local (ofString "nlen"),.var .local (ofString "o_rq")]]

theorem source_stateless_request_call : statelessAt 28 =
    .decCall (ofString "rq") .one (ofString "decode_requests") statelessRequestArguments
      (statelessAt 29) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The request decoder and the full witness suffix are bounded by the
outer input length plus 378, including every rejection and heap failure. -/
theorem evaluate_stateless_request_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset requestPointer requestLength offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      statelessRequestArguments = some [.val (.word requestPointer),.val (.word requestLength)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (ordered : offset ≤ length) (budget : length.toNat + 378 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 28)
    state.clock ≤ evaluated.2.clock + (length.toNat + 378) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_stateless_request_call]
  have cost : 355 + (length.toNat + 23) = length.toNat + 378 := by omega
  rw [← cost]
  apply evaluate_decodeRequests_declaration_continuation_bounded state (ofString "rq") (statelessAt 29)
    (length.toNat + 23) statelessRequestArguments requestPointer requestLength offsets heapPointer
    arguments atOffsets code heap heapBound (by omega)
  intro value ready nextHeap locals installed domain nextGlobal nextBound other enough
  apply evaluate_stateless_request_store_bounded ready pointer length offset offsets nextHeap
    ?_ ?_ ?_ ((other _ (by decide)).trans atOffsets) nextGlobal nextBound (installed.trans code) ordered enough
  all_goals rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,atPointer,atLength,atOffset,
    show ofString "rq" ≠ ofString "p" by decide,
    show ofString "rq" ≠ ofString "len" by decide,
    show ofString "rq" ≠ ofString "o_wit" by decide]

#print axioms evaluate_stateless_request_call_bounded
end InitECandidate.Runtime
