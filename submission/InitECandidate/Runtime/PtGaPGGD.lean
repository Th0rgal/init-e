import InitECandidate.Runtime.PtPGStepGD
/-!
The creation-branch `sa = get_account(sender)` of `process_transaction` in the final phase: `accountRegT_aqmh` is
instantiated with the arena bound raised to the current heap pointer `Hc` and the outside words `OutX Out Lo Hg`, then
lowered back to `P0`. Its kept words (`GaKeep`) cover the outside words, the `ko` table, and the fresh segment words
`[Lo, Hg)` (off the workspace, which lies below `P0`), so `PG` (at the exit heap pointer) and the `aa` table survive.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section gp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Hg Hb Nj Ts Bs : BitVec 64} {M0 : Mem}

theorem aqgd_decCall_getAccount_pg {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name xname : MlS)
    {cont : ProgHOL 64} (Taa Pa : BitVec 64)
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat)
    (hP0Lo : P0.toNat ≤ Lo.toNat) (hLoT : Lo.toNat ≤ Taa.toNat) (hLoHg : Lo.toNat ≤ Hg.toNat) (hPa : Pa.toNat ≤ Hg.toNat)
    (hgb : Hg.toNat ≤ Hb.toNat)
    (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hx : ∀ L, LP L → ∃ X : BitVec 64, L.lookup xname = some (.val (.word X)))
    (hup : ∀ L (y : BitVec 64), LP L → LP' (L.update (name,.val (.word y))))
    (hcont : ∀ Hb' : BitVec 64, Hb.toNat ≤ Hb'.toNat →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (LP' L ∧ PG n c T Out ko D B Excl Lo Hg Hb' Nj M0 M G) ∧ TabV Taa Taa Pa M) Q RR cont)
    (hres : ∀ L M G L' M' G', (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M →
      Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) ∧ TabV Taa Taa Pa M) Q2 RR
      (.decCall name .one (ofString "get_account") [.var .local xname] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ (H1 : BitVec 64) (l : Fin n → TLay), HeapIs G0' H1 ∧ Hb.toNat ≤ H1.toNat ∧
        RegPure n c T (OutX Out Lo Hg) H1 l ∧ RegMem n c T l M0' ∧ TCont D B M0' (T ko) (l ko) ∧
        (∀ x, (l ko).arr x → x.toNat < H1.toNat) ∧
        (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
          ((Reg n c T (OutX Out Lo Hg) H' M' ∧ H1.toNat ≤ H'.toNat) ∧
            ∀ x, GaKeep SP0 H1 FM K Pd NB (OutX Out Lo Hg) (T ko) (l ko) x → M' x = M0' x)))
    (Pc := fun L M G => ∃ Hb' : BitVec 64, ((LP' L ∧ PG n c T Out ko D B Excl Lo Hg Hb' Nj M0 M G) ∧
      TabV Taa Taa Pa M) ∧ Hb.toNat ≤ Hb'.toNat) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_
    (aqgd_exE (fun Hb' => aqgd_pureE (fun le => hcont Hb' le))) hres
  · intro L0 M0' G0' ⟨⟨_,⟨H1,hH,hb1⟩,reg,hn,_⟩,_⟩
    obtain ⟨l,pure,mem,tc,ab⟩ := regT_mono reg hb1
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H1.toNat) (fun _ _ g aw ⟨_,_,hg⟩ => by
      subst hg; exact (jws_heap_facts aw.1.1.1 hH).1) ?_
    intro p1
    refine aqgd_conseq (aqgd_jwsbus (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_lower p1 (accountRegT_aqmh (P0 := H1) (SP0 := SP0) (FM := FM) (G0 := G0) (w := w) n c T kA kB ko hAB
        hAo hBo Ts Bs hTs hBs hcA hcB (OutX Out Lo Hg) (Or.inl hOut) H1 (le_refl _) K Pd NB hK0 hPd0 hNB0 safe
        (hOutSafe w hOut).1 (by omega) l pure M0' mem ab)))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_account_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_account_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨hn,H1,hH,⟨⟨ha,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩,rfl⟩
    · intro v M' G' ⟨post,_⟩
      exact ⟨H1,l,hH,hb1,pure,mem,tc,ab,post⟩
  · intro F s values callee rs _ H _ ⟨⟨lp,_⟩,_⟩ _ args lookup
    obtain ⟨X,hX⟩ := hx _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hX] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨X,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨lp,⟨H0',hH0',_⟩,_,_,fr⟩,tv⟩ ⟨H1,l,hH',hb1,pure,mem,tc,ab,hn',H',hH2,⟨reg,hle'⟩,frG⟩ ok
    have e := heapIs_unique hH0' hH'
    subst e
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => frG x (Or.inl ⟨hx,hkoWs M (l ko) (mem ko).2 x hx⟩)
    refine ⟨H',⟨⟨hup L y lp,⟨⟨H',hH2,le_refl _⟩,regT_of_reg l pure tc ab reg hle' keepT,hn',
      fun x ho hxe => (frG x (Or.inr ⟨Or.inl ho,(hOutSafe x ho).1,by have := (hOutSafe x ho).2; omega⟩)).trans
        (fr x ho hxe)⟩⟩,tabV_frame tv (fun x lo hi => frG x (Or.inr ⟨Or.inr ⟨by omega,by omega⟩,
          hWsP0 x (by omega),by omega⟩))⟩,by omega⟩

#print axioms aqgd_decCall_getAccount_pg
end gp
end InitECandidate.Runtime
