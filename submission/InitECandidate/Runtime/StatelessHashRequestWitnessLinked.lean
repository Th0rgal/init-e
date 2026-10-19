import InitECandidate.Runtime.StatelessHashRequestWitnessReturned
import InitECandidate.Runtime.StatelessRequestWitnessLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Hash-count validation and the concrete outer-header stores lead to the
actual request-table link exported through the witness decoder. -/
theorem stateless_hash_request_witness_linked {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    (small : (NL - ORQ).toNat ≤ 134217712)
    (scratchBefore : offsets.toNat + 24 ≤ S.toNat) (siBefore : S.toNat + 88 ≤ H.toNat)
    (run : evaluateHOLFiniteState t (statelessAt 24) = (some (.returned v), post)) :
    post.memaddrs (S + (32#64)) ∧ post.memory (S + (32#64)) = .word H ∧ HtrRequestsDecoded post H := by
  have run' : evaluateHOLFiniteState t (reqCount "nvh" "o_rq" "o_vh" 32 (statelessAt 25)) = (some (.returned v), post) := by
    rw [← run, source_stateless_hash_count]; rfl
  obtain ⟨mod, t1, out1, ⟨m1, g1, d1, c1, k1, n1⟩, r1, pm1, pg1, _⟩ :=
    reqCount_returned t post "nvh" "o_rq" "o_vh" 32 (statelessAt 25) ORQ OVH v horq hovh code (by decide) run'
  have nv : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "nvh" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  have t1np := (k1 _ (nv "np" (by simp))).trans hnp
  have t1nlen := (k1 _ (nv "nlen" (by simp))).trans hnlen
  have t1ovh := (k1 _ (nv "o_vh" (by simp))).trans hovh
  have t1orq := (k1 _ (nv "o_rq" (by simp))).trans horq
  have t1p := (k1 _ (nv "p" (by simp))).trans hp
  have t1len := (k1 _ (nv "len" (by simp))).trans hlen
  have t1ow := (k1 _ (nv "o_wit" (by simp))).trans howit
  have t1si := (k1 _ (nv "si" (by simp))).trans hsi
  obtain ⟨a25, a26, a27⟩ := source_stateless_hash_stores_exact
  rw [a25] at r1
  obtain ⟨dom8, r2⟩ := seqStore_returned_exact t1 out1 _ _ _ (S + 8) (NP + OVH) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, evalListHOLExact, t1np, t1ovh, wordOpHOL, wordOp, valueIsWord, valueWord]) r1
  rw [a26] at r2
  obtain ⟨dom16, r3⟩ := seqStore_returned_exact _ out1 _ _ _ (S + 16) ((ORQ - OVH) / 32) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, n1]) r2
  rw [a27] at r3
  obtain ⟨dom24, r4⟩ := seqStore_returned_exact _ out1 _ _ _ (S + 24) (NP + 8) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, evalListHOLExact, t1np, wordOpHOL, wordOp, valueIsWord, valueWord]) r3
  generalize ht4 : ({({({t1 with memory := wmem t1.memory (S + 8) (NP + OVH)} : PanSemStateFiniteExact 64 F) with
    memory := wmem (wmem t1.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)} : PanSemStateFiniteExact 64 F) with
    memory := wmem (wmem (wmem t1.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)) (S + 24) (NP + 8)} :
      PanSemStateFiniteExact 64 F) = t4 at r4
  have t4l : t4.locals = t1.locals := by rw [← ht4]
  have t4g : t4.globals = t.globals := by rw [← ht4]; exact g1
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact c1.trans code
  have t4m : t4.memory = wmem (wmem (wmem t.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)) (S + 24) (NP + 8) := by
    rw [← ht4, m1]
  have linked := stateless_request_witness_linked t4 out1 NP NL ORQ P L OW S offsets H v t4c
    (by rw [t4l]; exact t1np) (by rw [t4l]; exact t1nlen) (by rw [t4l]; exact t1orq) (by rw [t4l]; exact t1p)
    (by rw [t4l]; exact t1len) (by rw [t4l]; exact t1ow) (by rw [t4l]; exact t1si) (by rw [t4g]; exact hg)
    (by rw [t4g]; exact heap) hb small scratchBefore siBefore r4
  have metadata := evaluateHOLFiniteState_metadata t (statelessAt 24)
  rw [run] at metadata
  have metadataOut := evaluateHOLFiniteState_metadata t4 (statelessAt 28)
  rw [r4] at metadataOut
  have domain : post.memaddrs = out1.memaddrs := by
    rw [metadata.2.1,metadataOut.2.1,← ht4,d1]
  exact ⟨by rw [domain]; exact linked.1,by rw [pm1]; exact linked.2.1,linked.2.2.after_frame pm1 domain⟩

#print axioms stateless_hash_request_witness_linked
end InitECandidate.Runtime
