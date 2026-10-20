import InitECandidate.Runtime.RequestsDeclarationHeapUpper
import InitECandidate.Runtime.StatelessWitnessHeapUpper
import InitECandidate.Runtime.PayloadDeclarationHeapUpper
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem stateless_request_heap_upper {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (NP NL ORQ P L OW S offsets H : BitVec 64) (v : ValueHOL 64) (code : t.code = originalRuntimeCode)
    (hnp : t.locals.lookup (ofString "np") = some (.val (.word NP)))
    (hnlen : t.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (horq : t.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word P)))
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word L)))
    (howit : t.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (hsi : t.locals.lookup (ofString "si") = some (.val (.word S)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (hb : H.toNat ≤ 33806089496) (ha : H.toNat % 8 = 0)
    (run : evaluateHOLFiniteState t (statelessAt 28) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat ≤ Hf.toNat ∧Hf.toNat≤H.toNat+12*(L-OW).toNat+108 := by
  have nrq : ∀ n : String, n ∈ ["si", "p", "len", "o_wit"] → ofString n ≠ ofString "rq" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_request_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessRequestArguments = some [.val (.word (NP + ORQ)), .val (.word (NL - ORQ))] := by
    simp [statelessRequestArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hnlen, horq,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, k1, rq1, c1, mem1, ⟨H1, hh1, g1, b1, a1, upper1, oth1⟩, r1, pg1, pm1⟩ :=
    ret_requestsDecl_heap_upper t post (ofString "rq") _ _ (NP + ORQ) (NL - ORQ) H offsets v code args heap hg hb run
  have t1si := (k1 _ (nrq "si" (by simp))).trans hsi
  have t1p := (k1 _ (nrq "p" (by simp))).trans hp
  have t1len := (k1 _ (nrq "len" (by simp))).trans hlen
  have t1ow := (k1 _ (nrq "o_wit" (by simp))).trans howit
  -- si+32 store
  rw [source_stateless_request_store, evaluateHOLFiniteState_seq_line780] at r1
  unfold statelessRequestStore at r1
  have addr : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
      (.op .add [.var .local (ofString "si"), .const 32]) = some (.val (.word (S + 32))) := by
    simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]
  have frame2 := fun (w : BitVec 64) (hw : w ≠ S + 32) => evaluate_wordStore_memory_frame t1 _
    (.var .local (ofString "rq")) (S + 32) w addr (fun parsed h => by simp [evalHOLExact, rq1] at h; exact ⟨_, h.symm⟩) hw
  rcases evaluate_store_cases t1 (.op .add [.var .local (ofString "si"), .const 32]) (.var .local (ofString "rq"))
    with err | ⟨M, ok⟩
  · rw [err] at r1; simp at r1
  rw [ok] at r1 frame2
  dsimp only at r1
  generalize ht2 : ({t1 with memory := M} : PanSemStateFiniteExact 64 F) = t2 at r1 frame2
  have t2l : t2.locals = t1.locals := by rw [← ht2]
  have t2g : t2.globals = t1.globals := by rw [← ht2]
  have t2c : t2.code = t1.code := by rw [← ht2]
  -- wp and wlen
  rw [source_stateless_witness_pointer] at r1
  obtain ⟨val3, o3, init3, r3, e3⟩ := evaluate_dec_returned_scope t2 o1 (ofString "wp") .one _ _ v r1
  have i3 : @evalHOLExact 64 F _ t2.toExact (fun x => Classical.propDecidable (t2.memaddrs x))
      (.op .add [.var .local (ofString "p"), .var .local (ofString "o_wit")]) = some (.val (.word (P + OW))) := by
    simp [evalHOLExact, evalListHOLExact, t2l, t1p, t1ow, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [i3] at init3
  obtain rfl := (Option.some.inj init3).symm
  rw [source_stateless_witness_length] at r3
  obtain ⟨val4, o4, init4, r4, e4⟩ := evaluate_dec_returned_scope _ o3 (ofString "wlen") .one _ _ v r3
  have wpl : ofString "len" ≠ ofString "wp" := by decide_cbv
  have wpo : ofString "o_wit" ≠ ofString "wp" := by decide_cbv
  have i4 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "wp") (.val (.word (P + OW))) t2).toExact
      (fun x => Classical.propDecidable _)
      (.op .sub [.var .local (ofString "len"), .var .local (ofString "o_wit")]) = some (.val (.word (L - OW))) := by
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wpl, wpo, Ne.symm wpl, Ne.symm wpo, t2l, t1len, t1ow, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [i4] at init4
  obtain rfl := (Option.some.inj init4).symm
  generalize ht4 : setVarHOLFinite (ofString "wlen") (.val (.word (L - OW)))
    (setVarHOLFinite (ofString "wp") (.val (.word (P + OW))) t2) = t4 at r4
  have siw : ofString "si" ≠ ofString "wp" := by decide_cbv
  have siwl : ofString "si" ≠ ofString "wlen" := by decide_cbv
  have wwl : ofString "wp" ≠ ofString "wlen" := by decide_cbv
  have t4wp : t4.locals.lookup (ofString "wp") = some (.val (.word (P + OW))) := by
    rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wwl, Ne.symm wwl]
  have t4wl : t4.locals.lookup (ofString "wlen") = some (.val (.word (L - OW))) := by rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have t4si : t4.locals.lookup (ofString "si") = some (.val (.word S)) := by
    rw [← ht4]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, siw, siwl, Ne.symm siw, Ne.symm siwl, t2l, t1si]
  have t4g : t4.globals = t1.globals := by rw [← ht4]; exact t2g
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact t2c.trans (c1.trans code)
  have t4m : ∀ w, t4.memory w = t2.memory w := by intro w; rw [← ht4]; rfl
  have hhs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
  have t4off : t4.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [t4g, oth1 _ (Ne.symm hhs)]; exact hg
  have t4heap : t4.globals.lookup (ofString "heap_ptr") = some (.val (.word H1)) := by rw [t4g]; exact hh1
  obtain ⟨Hf, hf1, hf2, upperFinal⟩ := stateless_witness_heap_upper t4 o4 _ _ S offsets H1 v t4c t4wp t4wl t4si t4off
    t4heap b1 a1 r4
  have og : post.globals = o4.globals := by
    rw [pg1, e3]; show o3.globals = _; rw [e4]
  exact ⟨Hf, by rw [og]; exact hf1, by omega,by omega⟩

theorem stateless_hash_heap_upper {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    ∃ Hf : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word Hf)) ∧ H.toNat ≤ Hf.toNat ∧Hf.toNat≤H.toNat+12*(L-OW).toNat+108 := by
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
  obtain ⟨Hf, hf1, hf2, upperFinal⟩ := stateless_request_heap_upper t4 out1 NP NL ORQ P L OW S offsets H v t4c
    (by rw [t4l]; exact t1np) (by rw [t4l]; exact t1nlen) (by rw [t4l]; exact t1orq) (by rw [t4l]; exact t1p)
    (by rw [t4l]; exact t1len) (by rw [t4l]; exact t1ow) (by rw [t4l]; exact t1si) (by rw [t4g]; exact hg)
    (by rw [t4g]; exact heap) hb ha r4
  exact ⟨Hf, by rw [pg1]; exact hf1, hf2,upperFinal⟩

#print axioms stateless_hash_heap_upper

theorem stateless_payload_suffix_heap_upper {F : Type} (t post : PanSemStateFiniteExact 64 F)
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
    (scratchBelow : offsets.toNat+32≤H.toNat)
    (payloadFits : (NP + OPL).toNat + (OVH - OPL).toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState t (statelessAt 22) = (some (.returned v), post)) :
    ∃ Hf : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word Hf)) ∧
      H.toNat≤Hf.toNat ∧Hf.toNat≤H.toNat+4*(OVH-OPL).toNat+12*(L-OW).toNat+251 := by
  have nl : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "pl" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      statelessPayloadArguments = some [.val (.word (NP + OPL)), .val (.word (OVH - OPL))] := by
    simp [statelessPayloadArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, hnp, hopl, hovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨t1, o1, nH, arr, cnt, m32, m40, cntB, arrB, slices1, above1, k1, pl1, c1, d1, long, m0, m8, nh1, nb1, na1, grow1, g1, frame1, r1, pg1, pm1, _, payloadUpper⟩ :=
    ret_payloadDecl_heap_upper t post (ofString "pl") _ _ (NP + OPL) (OVH - OPL) offsets H v code args hg heap hb ha heapArena
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
  have hs : ofString "heap_ptr"≠ofString "ssz_offs" := by decide
  obtain ⟨Hf,hfinal,lower,upper⟩:=stateless_hash_heap_upper t2 o1 NP NL OVH ORQ P L OW S offsets nH v t2c
    (by rw [t2l];exact (k "np" (by simp)).trans hnp) (by rw [t2l];exact (k "nlen" (by simp)).trans hnlen)
    (by rw [t2l];exact (k "o_vh" (by simp)).trans hovh) (by rw [t2l];exact (k "o_rq" (by simp)).trans horq)
    (by rw [t2l];exact (k "p" (by simp)).trans hp) (by rw [t2l];exact (k "len" (by simp)).trans hlen)
    (by rw [t2l];exact (k "o_wit" (by simp)).trans howit) (by rw [t2l];exact (k "si" (by simp)).trans hsi)
    (by rw [t2g,g1 _ (Ne.symm hs)];exact hg) (by rw [t2g];exact nh1) nb1 na1 r2
  exact ⟨Hf,by rw [pg1];exact hfinal,by omega,by omega⟩
#print axioms stateless_payload_suffix_heap_upper
#print axioms stateless_request_heap_upper
end InitECandidate.Runtime
