import InitECandidate.Runtime.StatelessPayloadSuffixReturnedCells
import InitECandidate.Runtime.StatelessPayloadStoreRequestHeapExtent
import InitECandidate.Runtime.StatelessPayloadStoreRequestsLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original payload declaration and full remaining stateless decoder
export the execution-linked request table, allocated after the payload. -/
theorem stateless_payload_suffix_request_heap_extent {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL OPL OVH ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (hopl : t.locals.lookup (ofString "o_pl") = some (.val (.word OPL)))
    (hovh : t.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (heapArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → H.toNat ≤ a.toNat → a.toNat < 33806089496 → t.memaddrs a)
    (scratchDom : t.memaddrs (offsets + 0) ∧ t.memaddrs (offsets + 8) ∧ t.memaddrs (offsets + 16) ∧
      t.memaddrs (offsets + 24))
    (scratchBelow : offsets.toNat + 40 ≤ S.toNat) (siBelow : S.toNat + 96 ≤ H.toNat)
    (small : (NL - ORQ).toNat ≤ 134217712)
    (payloadFits : (NP + OPL).toNat + (OVH - OPL).toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (statelessAt 22) = (some (.returned v), post)) :
    ∃ record : BitVec 64, H.toNat + 136 ≤ record.toNat ∧
      post.memaddrs (S + (32#64)) ∧ post.memory (S + (32#64)) = .word record ∧ HtrRequestsDecoded post record ∧
      ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧ record.toNat + 80 ≤ finalHeap.toNat := by
  have nl : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "pl" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessPayloadArguments = some [.val (.word (NP + OPL)), .val (.word (OVH - OPL))] := by
    simp [statelessPayloadArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hopl, hovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, nH, arr, cnt, m32, m40, cntB, arrB, slices1, above1, k1, pl1, c1, d1, long, m0, m8, nh1, nb1, na1, grow1, g1, frame1, r1, pg1, pm1, domain⟩ :=
    ret_payloadDecl_cells t post (ofString "pl") _ _ (NP + OPL) (OVH - OPL) offsets H v code args hg heap hb ha heapArena
      scratchDom (by omega) payloadFits run
  have k : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      t1.locals.lookup (ofString n) = t.locals.lookup (ofString n) := fun n hn => k1 _ (nl n hn)
  have linked := stateless_payload_store_requests_linked t1 o1 NP NL OVH ORQ P L OW S offsets nH v (c1.trans code)
    ((k "np" (by simp)).trans hnp) ((k "nlen" (by simp)).trans hnlen)
    ((k "o_vh" (by simp)).trans hovh) ((k "o_rq" (by simp)).trans horq)
    ((k "p" (by simp)).trans hp) ((k "len" (by simp)).trans hlen)
    ((k "o_wit" (by simp)).trans howit) ((k "si" (by simp)).trans hsi)
    ((g1 _ (by decide)).trans hg) nh1 nb1 na1 small (by omega) (by omega) H pl1 r1
  obtain ⟨finalHeap,binding,extent⟩ := stateless_payload_store_request_heap_extent t1 o1 NP NL OVH ORQ P L OW S offsets nH v (c1.trans code)
    ((k "np" (by simp)).trans hnp) ((k "nlen" (by simp)).trans hnlen)
    ((k "o_vh" (by simp)).trans hovh) ((k "o_rq" (by simp)).trans horq)
    ((k "p" (by simp)).trans hp) ((k "len" (by simp)).trans hlen)
    ((k "o_wit" (by simp)).trans howit) ((k "si" (by simp)).trans hsi)
    ((g1 _ (by decide)).trans hg) nh1 nb1 na1 H pl1 r1
  exact ⟨nH,grow1,by rw [domain]; exact linked.1,by rw [pm1]; exact linked.2.1,linked.2.2.after_frame pm1 domain,
    finalHeap,by rw [pg1]; exact binding,extent⟩

#print axioms stateless_payload_suffix_request_heap_extent
end InitECandidate.Runtime
