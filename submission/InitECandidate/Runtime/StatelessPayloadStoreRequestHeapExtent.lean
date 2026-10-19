import InitECandidate.Runtime.StatelessHashRequestHeapExtent
import InitECandidate.Runtime.StatelessPayloadStoreBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual payload-pointer store and complete following suffix retain the
link between the outer header and decoded request table. -/
theorem stateless_payload_store_request_heap_extent {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL OVH ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (hovh : t.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (payload : BitVec 64) (atPayload : t.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (run : evaluateHOLFiniteState t (statelessAt 23) = (some (.returned v), post)) :
    ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧ H.toNat + 80 ≤ finalHeap.toNat := by
  rw [source_stateless_payload_store] at run
  unfold statelessPayloadStore at run
  obtain ⟨_,tail⟩ := seqStore_returned_exact t post _ _ _ (S + 0) payload v
    (by simp [evalHOLExact,evalListHOLExact,hsi,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atPayload]) run
  let entry : PanSemStateFiniteExact 64 F := {t with memory := wmem t.memory (S + 0) payload}
  exact stateless_hash_request_heap_extent entry post NP NL OVH ORQ P L OW S offsets H v code
    hnp hnlen hovh horq hp hlen howit hsi hg heap hb ha tail

#print axioms stateless_payload_store_request_heap_extent
end InitECandidate.Runtime
