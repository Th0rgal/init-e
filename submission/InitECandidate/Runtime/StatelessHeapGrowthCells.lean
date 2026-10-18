import InitECandidate.Runtime.StatelessHeapGrowth
import InitECandidate.Runtime.StatelessPayloadSuffixReturnedCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000000
theorem stateless_payload_suffix_final_heap_cells {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    (payloadFits : (NP + OPL).toNat + (OVH - OPL).toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (statelessAt 22) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat + 136 ≤ Hf.toNat ∧
      ∀ array count : BitVec 64, post.memory (H + 32) = .word array → post.memory (H + 40) = .word count →
        array.toNat + count.toNat * 16 ≤ Hf.toNat := by
  have nl : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "pl" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessPayloadArguments = some [.val (.word (NP + OPL)), .val (.word (OVH - OPL))] := by
    simp [statelessPayloadArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hopl, hovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, nH, arr, cnt, m32, m40, cntB, arrB, slices1, above1, k1, pl1, c1, d1, long, m0, m8, nh1, nb1, na1, grow1, g1, frame1, r1, pg1, pm1, _⟩ :=
    ret_payloadDecl_cells t post (ofString "pl") _ _ (NP + OPL) (OVH - OPL) offsets H v code args hg heap hb ha heapArena
      scratchDom (by omega) payloadFits run
  have k : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      t1.locals.lookup (ofString n) = t.locals.lookup (ofString n) := fun n hn => k1 _ (nl n hn)
  -- si+0 store
  rw [source_stateless_payload_store] at r1
  unfold statelessPayloadStore at r1
  obtain ⟨dom0, r2⟩ := seqStore_returned_exact t1 o1 _ _ _ (S + 0) H v
    (by simp [evalHOLExact, evalListHOLExact, (k "si" (by simp)).trans hsi, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, pl1]) r1
  generalize ht2 : ({t1 with memory := wmem t1.memory (S + 0) H} : PanSemStateFiniteExact 64 F) = t2 at r2
  have t2l : t2.locals = t1.locals := by rw [← ht2]
  have t2g : t2.globals = t1.globals := by rw [← ht2]
  have t2c : t2.code = originalRuntimeCode := by rw [← ht2]; exact c1.trans code
  have t2m : t2.memory = wmem t1.memory (S + 0) H := by rw [← ht2]
  have hs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
  obtain ⟨hv, ⟨⟨Hf, hf1, hf2, hf3⟩, hfo⟩, mod, frame, cells, _⟩ := stateless_hash_request_witness_returned t2 o1
    NP NL OVH ORQ P L OW S offsets nH v t2c
    (by rw [t2l]; exact (k "np" (by simp)).trans hnp) (by rw [t2l]; exact (k "nlen" (by simp)).trans hnlen)
    (by rw [t2l]; exact (k "o_vh" (by simp)).trans hovh) (by rw [t2l]; exact (k "o_rq" (by simp)).trans horq)
    (by rw [t2l]; exact (k "p" (by simp)).trans hp) (by rw [t2l]; exact (k "len" (by simp)).trans hlen)
    (by rw [t2l]; exact (k "o_wit" (by simp)).trans howit) (by rw [t2l]; exact (k "si" (by simp)).trans hsi)
    (by rw [t2g, g1 _ (Ne.symm hs)]; exact hg) (by rw [t2g]; exact nh1) nb1 na1 r2
  obtain ⟨c8, c16, c24⟩ := cells scratchBelow (by omega)
  have sNat : ∀ c : BitVec 64, c.toNat ≤ 80 → (S + c).toNat = S.toNat + c.toNat := by
    intro c hc; rw [BitVec.toNat_add]; omega
  have hNat : ∀ c : BitVec 64, c.toNat ≤ 40 → (H + c).toNat = H.toNat + c.toNat := by
    intro c hc; rw [BitVec.toNat_add]; omega
  have oNat : ∀ q : BitVec 64, q.toNat < 5 → (offsets + q * 8).toNat = offsets.toNat + q.toNat * 8 := by
    intro q hq; rw [BitVec.toNat_add, BitVec.toNat_mul]; simp; omega
  -- payload header cells survive the At24 suffix
  have keepH : ∀ c : BitVec 64, c.toNat ≤ 40 → o1.memory (H + c) = t2.memory (H + c) := by
    intro c hc
    apply frame
    · rw [hNat c hc]; omega
    · intro q hq e; have := congrArg BitVec.toNat e; rw [hNat c hc, oNat q hq] at this; omega
    all_goals first
      | (intro e; have := congrArg BitVec.toNat e; rw [hNat c hc, sNat _ (by decide)] at this; simp at this; omega)
      | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          · intro e; have := congrArg BitVec.toNat e; rw [hNat c hc, sNat _ (by decide)] at this; simp at this; omega)
  have keepS0 : o1.memory (S + 0) = t2.memory (S + 0) := by
    apply frame
    · rw [sNat 0 (by decide)]; simp; omega
    · intro q hq e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), oNat q hq] at this; simp at this; omega
    all_goals first
      | (intro e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), sNat _ (by decide)] at this; simp at this)
      | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          · intro e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), sNat _ (by decide)] at this; simp at this)
  have neSH : ∀ c : BitVec 64, c.toNat ≤ 40 → S + 0 ≠ H + c := by
    intro c hc e; have := congrArg BitVec.toNat e; rw [sNat 0 (by decide), hNat c hc] at this; simp at this; omega
  obtain ⟨Hg, hg1, hg2⟩ := stateless_hash_heap t2 o1 NP NL OVH ORQ P L OW S offsets nH v t2c
    (by rw [t2l]; exact (k "np" (by simp)).trans hnp) (by rw [t2l]; exact (k "nlen" (by simp)).trans hnlen)
    (by rw [t2l]; exact (k "o_vh" (by simp)).trans hovh) (by rw [t2l]; exact (k "o_rq" (by simp)).trans horq)
    (by rw [t2l]; exact (k "p" (by simp)).trans hp) (by rw [t2l]; exact (k "len" (by simp)).trans hlen)
    (by rw [t2l]; exact (k "o_wit" (by simp)).trans howit) (by rw [t2l]; exact (k "si" (by simp)).trans hsi)
    (by rw [t2g, g1 _ (Ne.symm hs)]; exact hg) (by rw [t2g]; exact nh1) nb1 na1 r2
  refine ⟨Hg, by rw [pg1]; exact hg1, by omega, fun array count h32 h40 => ?_⟩
  have e32 : post.memory (H + 32) = .word arr := by
    rw [pm1, keepH 32 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 32 (by decide)))]; exact m32
  have e40 : post.memory (H + 40) = .word cnt := by
    rw [pm1, keepH 40 (by decide), t2m]; simp only [wmem, if_neg (Ne.symm (neSH 40 (by decide)))]; exact m40
  rw [e32] at h32; rw [e40] at h40
  injection h32 with a; injection h40 with b
  subst a; subst b
  omega

#print axioms stateless_payload_suffix_final_heap_cells
end InitECandidate.Runtime
