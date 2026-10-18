import InitECandidate.Runtime.StatelessRequestsWitnessReturned
import InitECandidate.Runtime.DecodeRequestsCountsReturned
import InitECandidate.Runtime.StatelessHashCountBound
import InitECandidate.Runtime.StatelessHashStoresBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem seqStore_returned_exact {F : Type} (t post : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) (rest : ProgHOL 64)
    (A X : BitVec 64) (v : ValueHOL 64)
    (hd : @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) d = some (.val (.word A)))
    (he : @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e = some (.val (.word X)))
    (run : evaluateHOLFiniteState t (.seq (.store d e) rest) = (some (.returned v), post)) :
    t.memaddrs A ∧ evaluateHOLFiniteState ({t with memory := wmem t.memory A X} : PanSemStateFiniteExact 64 F) rest =
      (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  by_cases dom : t.memaddrs A
  · rw [sszStore_in t A X d e hd he dom] at run; exact ⟨dom, run⟩
  · rw [sszStore_out t A X d e hd he dom] at run; simp at run

theorem source_stateless_hash_stores_exact : statelessAt 25 =
    .seq (.store (.op .add [.var .local (ofString "si"),.const 8])
      (.op .add [.var .local (ofString "np"),.var .local (ofString "o_vh")]))
    (statelessAt 26) ∧
    statelessAt 26 = .seq (.store (.op .add [.var .local (ofString "si"),.const 16]) (.var .local (ofString "nvh")))
      (statelessAt 27) ∧
    statelessAt 27 = .seq (.store (.op .add [.var .local (ofString "si"),.const 24])
        (.op .add [.var .local (ofString "np"),.const 8])) (statelessAt 28) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [statelessAt,statelessNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl

theorem bv_add_ne (S : BitVec 64) (a b : BitVec 64) (h : a ≠ b) : S + a ≠ S + b := by
  rw [Ne, BitVec.add_right_inj]; exact h

/-- Every returned run of the actual original stateless suffix At24..At48. -/
theorem stateless_hash_request_witness_returned {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState t (statelessAt 24) = (some (.returned v), post)) :
    v = .val (.word S) ∧ HeapFrame t post ∧ (ORQ - OVH) % 32 = 0 ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → (∀ k : BitVec 64, k.toNat < 5 → w ≠ offsets + k * 8) →
        w ≠ S + 8 → w ≠ S + 16 → w ≠ S + 24 → w ≠ S + 32 →
        (w ≠ S + 40 ∧ w ≠ S + 48 ∧ w ≠ S + 56 ∧ w ≠ S + 64 ∧ w ≠ S + 72 ∧ w ≠ S + 80) →
        post.memory w = t.memory w) ∧
      (offsets.toNat + 40 ≤ S.toNat → S.toNat + 96 ≤ H.toNat →
        post.memory (S + 8) = .word (NP + OVH) ∧ post.memory (S + 16) = .word ((ORQ - OVH) / 32) ∧
        post.memory (S + 24) = .word (NP + 8)) ∧
      t.memaddrs (S + 8) ∧ t.memaddrs (S + 16) ∧ t.memaddrs (S + 24) := by
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
  obtain ⟨hv, frame, memf⟩ := stateless_request_witness_returned t4 out1 NP NL ORQ P L OW S offsets H v t4c
    (by rw [t4l]; exact t1np) (by rw [t4l]; exact t1nlen) (by rw [t4l]; exact t1orq) (by rw [t4l]; exact t1p)
    (by rw [t4l]; exact t1len) (by rw [t4l]; exact t1ow) (by rw [t4l]; exact t1si) (by rw [t4g]; exact hg)
    (by rw [t4g]; exact heap) hb ha r4
  have pm : post.memory = out1.memory := pm1
  have pg : post.globals = out1.globals := pg1
  refine ⟨hv, ?_, mod, ?_, ?_, by rw [← d1]; exact dom8, by rw [← d1]; exact dom16, by rw [← d1]; exact dom24⟩
  · obtain ⟨⟨H', h1, h2, h3⟩, h4⟩ := frame
    exact ⟨⟨H', by rw [pg]; exact h1, h2, h3⟩, fun k hk => by rw [pg, h4 k hk, t4g]⟩
  · intro w below scratch s8 s16 s24 s32 headers
    rw [pm, memf w below scratch s32 headers, t4m]
    simp only [wmem, if_neg s8, if_neg s16, if_neg s24]
  · intro scratchBelow siBelow
    have e816 : S + 8 ≠ S + 16 := bv_add_ne S 8 16 (by decide)
    have e824 : S + 8 ≠ S + 24 := bv_add_ne S 8 24 (by decide)
    have e1624 : S + 16 ≠ S + 24 := bv_add_ne S 16 24 (by decide)
    have sNat : ∀ c : BitVec 64, c.toNat ≤ 80 → (S + c).toNat = S.toNat + c.toNat := by
      intro c hc; rw [BitVec.toNat_add]; omega
    have oNat : ∀ k : BitVec 64, k.toNat < 5 → (offsets + k * 8).toNat = offsets.toNat + k.toNat * 8 := by
      intro k hk; rw [BitVec.toNat_add, BitVec.toNat_mul]; simp; omega
    have cell : ∀ c : BitVec 64, 8 ≤ c.toNat → c.toNat ≤ 24 →
        post.memory (S + c) = t4.memory (S + c) := by
      intro c lo hi
      rw [pm]
      apply memf
      · rw [sNat c (by omega)]; omega
      · intro k hk e; have := congrArg BitVec.toNat e; rw [sNat c (by omega), oNat k hk] at this; omega
      · intro e; have := congrArg BitVec.toNat e; rw [sNat c (by omega), sNat 32 (by decide)] at this; simp at this; omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · intro e; have := congrArg BitVec.toNat e
          rw [sNat c (by omega), sNat _ (by decide)] at this; simp at this; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [cell 8 (by decide) (by decide), t4m]
      simp [wmem, e816, e824]
    · rw [cell 16 (by decide) (by decide), t4m]
      simp [wmem, e1624]
    · rw [cell 24 (by decide) (by decide), t4m]
      simp [wmem]

#print axioms stateless_hash_request_witness_returned
end InitECandidate.Runtime
