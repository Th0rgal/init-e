import InitECandidate.Runtime.PtTabGD
/-!
The actual `htab_set(t, key, value)` on a fresh segment table at the call site: from `TBf Tt A` (a valid table in
`[A, P)`, `P` at most the heap pointer) with `A ≥ Lo`, the call (`set_aqmh` at the arena bound raised to the current
heap pointer `Hc`, lowered back) keeps `SI`, re-establishes `TBf Tt A`, and keeps any property `R` framed by
"words outside `[A, P)` below `Hc` unchanged, heap pointer not decreasing".
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A valid fresh table at `Tt` in `[A, P)` with `P` at most the heap pointer. -/
def TBf (Tt A : BitVec 64) (M : Mem) (G : GA) : Prop :=
  ∃ P H : BitVec 64, TabV Tt A P M ∧ HeapIs G H ∧ P.toNat ≤ H.toNat

section hs
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

theorem aqgd_call_htabSet_si {LP : GA → Prop} {R : Mem → GA → Prop} (tn : MlS) (ek ev : ExpHOL 64)
    (Tt A : BitVec 64) (hLoA : Lo.toNat ≤ A.toNat) (hw : w.toNat < Lo.toNat)
    (ht : ∀ L, LP L → L.lookup tn = some (.val (.word Tt)))
    (hR : ∀ (M M' : Mem) (G G' : GA) (P H H' : BitVec 64), R M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x : BitVec 64, ¬ (A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) → x.toNat < H.toNat →
        M' x = M x) → R M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Tt A M G ∧ R M G)
      (fun L M G => (LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Tt A M G ∧ R M G) RR
      (.call (some (none,none)) (ofString "htab_set") [.var .local tn,ek,ev]) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ Kk V : BitVec 64, LK (irP0 Tt Kk V) L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ (P Hc KL SD Cc N KS VS US OS OPS : BitVec 64) (b : Nat), HeapIs G0' Hc ∧ P.toNat ≤ Hc.toNat ∧
        (HLay P Tt (Canon Tt Cc SD KS VS US OS OPS P) KL SD Cc N KS VS US OS OPS b ∧ A.toNat ≤ Tt.toNat ∧
          LayIn (fun x => A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) Cc SD KS VS US OS OPS) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          SetPost Tt (Canon Tt Cc SD KS VS US OS OPS Hc) M0' Cc SD KS VS US OS OPS Hc M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨⟨_,si⟩,⟨P,Hc,⟨KL,SD,Cc,N,KS,VS,US,OS,OPS,b,lay,hd,a,li⟩,hHc,le⟩,_⟩
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ Hc.toNat) (fun _ _ g aw ⟨_,_,hg⟩ => by
      subst hg; exact (jws_heap_facts aw.1.1.1 hHc).1) ?_
    intro hP0
    have hwF : ¬ Foot Hc Tt (Canon Tt Cc SD KS VS US OS OPS Hc) w := fun hc => by
      have := canon_ge a (fun y hy => let ⟨h1,h2⟩ := li y hy; ⟨h1,by omega⟩) (by have := lay.hdrP; omega) hc
      omega
    refine aqgd_conseq (P := fun L M G => ∃ Kk V : BitVec 64, LK (irP0 Tt Kk V) L ∧ M = M0' ∧ G = G0') ?_
      (fun _ _ _ ⟨⟨Kk,V,lk⟩,hm,hg⟩ => ⟨Kk,V,lk,hm,hg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_exE (fun Kk => aqgd_exE (fun V => ?_))
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J)
      (C := C) (N := Nj) originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_lower hP0 (set_aqmh (SP0 := SP0) (FM := FM) (G0 := G0) (P0 := Hc) Tt Kk V _ KL SD Cc N KS VS US OS OPS b
        (hlay_canon lay le) M0' hwF Hc (le_refl _)))))
      (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_hashSet_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_hashSet_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨lk,hM,hG⟩
      subst hM hG
      exact ⟨si.2.2.1,Hc,hHc,⟨lk,hd,rfl,rfl⟩,rfl⟩
    · intro v M' G' ⟨hn',H',hH',post⟩
      exact ⟨P,Hc,KL,SD,Cc,N,KS,VS,US,OS,OPS,b,hHc,le,⟨lay,a,li⟩,hn',H',hH',post⟩
  · intro F s values callee rs _ H hG ⟨⟨lp,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,ht _ lp] at ev1; subst ev1
    obtain ⟨_,Kk,V,_,rfl,rfl⟩ := entry3_words originalRuntimeCode_hashSet_lookup lookup
    have e := callee_eq originalRuntimeCode_hashSet_lookup lookup
    refine ⟨⟨Kk,V,fun p hp => ?_⟩,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨⟨lp,si⟩,_,r⟩ ⟨P,Hc,KL,SD,Cc,N,KS,VS,US,OS,OPS,b,hHc,le,⟨lay,a,li⟩,hn',H',hH',post⟩
    have hdrP := lay.hdrP
    obtain ⟨tv,leH,below⟩ := tabV_set a li le (by omega) post
    have fo := set_frame_out a li hdrP post
    refine ⟨⟨lp,si_glob (si_mem si (fun x hx => below x (by omega))) ⟨H',hH',?_⟩ hn'⟩,⟨H',H',tv,hH',le_refl _⟩,
      hR M M' G G' P Hc H' r hHc hH' leH fo⟩
    obtain ⟨H1,hH1,le1⟩ := si.1
    have := heapIs_unique hH1 hHc
    subst this
    omega

#print axioms aqgd_call_htabSet_si
end hs
end InitECandidate.Runtime
