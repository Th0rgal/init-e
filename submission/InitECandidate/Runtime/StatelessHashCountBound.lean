import InitECandidate.Runtime.StatelessHashStoresBound
import InitECandidate.Runtime.SszFixedListCountContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def statelessHashCountArguments : List (ExpHOL 64) :=
  [.op .sub [.var .local (ofString "o_rq"),.var .local (ofString "o_vh")],.const 32,.const 9223372036854775807]

theorem source_stateless_hash_count : statelessAt 24 =
    .decCall (ofString "nvh") .one (ofString "ssz_fixed_list_count") statelessHashCountArguments
      (statelessAt 25) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The fixed-size hash-list count, header stores, request decoder and
complete witness decoder consume at most input length plus 445 clocks. -/
theorem evaluate_stateless_hash_count_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offset np nlen rqOffset vhOffset offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffset : state.locals.lookup (ofString "o_wit") = some (.val (.word offset)))
    (atNp : state.locals.lookup (ofString "np") = some (.val (.word np)))
    (atNlen : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (atRqOffset : state.locals.lookup (ofString "o_rq") = some (.val (.word rqOffset)))
    (atVhOffset : state.locals.lookup (ofString "o_vh") = some (.val (.word vhOffset)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (ordered : offset ≤ length) (budget : length.toNat + 445 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 24)
    state.clock ≤ evaluated.2.clock + (length.toNat + 445) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      statelessHashCountArguments = some [.val (.word (rqOffset - vhOffset)),.val (.word 32),.val (.word 9223372036854775807)] := by
    simp [statelessHashCountArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atRqOffset,atVhOffset,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_stateless_hash_count]
  have cost : 67 + (length.toNat + 378) = length.toNat + 445 := by omega
  rw [← cost]
  apply evaluate_sszFixedListCount_continuation_bounded state (ofString "nvh") (statelessAt 25)
    (length.toNat + 378) statelessHashCountArguments (rqOffset - vhOffset) 32 9223372036854775807
    arguments code (by decide) (by omega)
  intro value ready locals installed domain memory globals enough
  apply evaluate_stateless_hash_stores_bounded ready pointer length offset np nlen rqOffset offsets heapPointer
    ?_ ?_ ?_ ?_ ?_ ?_ (by rw [globals]; exact atOffsets) (by rw [globals]; exact heap)
    heapBound (installed.trans code) ordered enough
  all_goals rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,atPointer,atLength,atOffset,
    atNp,atNlen,atRqOffset,
    show ofString "nvh" ≠ ofString "p" by decide,
    show ofString "nvh" ≠ ofString "len" by decide,
    show ofString "nvh" ≠ ofString "o_wit" by decide,
    show ofString "nvh" ≠ ofString "np" by decide,
    show ofString "nvh" ≠ ofString "nlen" by decide,
    show ofString "nvh" ≠ ofString "o_rq" by decide]

#print axioms evaluate_stateless_hash_count_bounded
end InitECandidate.Runtime
