import InitECandidate.Runtime.StatelessRequestStorePointer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual request and witness decoder suffix exports the request table
consumed by the initial hash, with counts bounded by the input arena. -/
theorem stateless_request_witness_linked {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (NP NL ORQ P L OW S offsets record : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (hnp : state.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : state.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (horq : state.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : state.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : state.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : state.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word record)))
    (heapBound : record.toNat ≤ 33806089496) (small : (NL - ORQ).toNat ≤ 134217712)
    (scratchBefore : offsets.toNat + 24 ≤ S.toNat) (siBefore : S.toNat + 88 ≤ record.toNat)
    (run : evaluateHOLFiniteState state (statelessAt 28) = (some (.returned value),post)) :
    post.memaddrs (S + (32#64)) ∧ post.memory (S + (32#64)) = .word record ∧
      HtrRequestsDecoded post record := by
  rw [source_stateless_request_call] at run
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      statelessRequestArguments = some [.val (.word (NP + ORQ)),.val (.word (NL - ORQ))] := by
    simp [statelessRequestArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,hnp,hnlen,horq,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨ready,output,kept,atRecord,readyCode,domain,decoded,⟨H,atHeap,extent,bound,aligned⟩,
      globals,tail,memory,postDomain⟩ := ret_requestsDecl_entries state post (ofString "rq") _ _
    (NP + ORQ) (NL - ORQ) record offsets value code arguments heap hg heapBound small run
  have result := stateless_request_store_preserves_entries ready output P L OW S offsets H record value
    (readyCode.trans code)
    ((kept _ (by decide_cbv)).trans hsi) ((kept _ (by decide_cbv)).trans hp)
    ((kept _ (by decide_cbv)).trans hlen) ((kept _ (by decide_cbv)).trans howit) atRecord
    ((globals _ (by decide_cbv)).trans hg) atHeap bound aligned extent (by omega) siBefore decoded tail
  have pointer := stateless_request_store_pointer ready output P L OW S offsets H record value
    (readyCode.trans code)
    ((kept _ (by decide_cbv)).trans hsi) ((kept _ (by decide_cbv)).trans hp)
    ((kept _ (by decide_cbv)).trans hlen) ((kept _ (by decide_cbv)).trans howit) atRecord
    ((globals _ (by decide_cbv)).trans hg) atHeap bound aligned (by omega) scratchBefore tail
  exact ⟨by rw [postDomain]; exact pointer.1,by rw [memory]; exact pointer.2,
    result.after_frame memory postDomain⟩

#print axioms stateless_request_witness_linked
end InitECandidate.Runtime
