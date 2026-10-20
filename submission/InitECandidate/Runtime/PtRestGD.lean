import InitECandidate.Runtime.PtSufEGD
import InitECandidate.Runtime.PtClearGD
/-!
The `process_transaction` remainder from `del = lds(out + 24)` on, in the final suffix state `PZ`: the prefix
final-phase state `PG` with the fresh suffix words `[Lo, Hg)` (`Lo` the heap pointer at spine drop 126, `Hg` the one at
`del`) as outside words of the registry, at any content heap pointer `Hb' ≥ Hg` and any journal counter. Registry
writers run at the arena bound raised to the current heap pointer (`aqgd_jws_lower`), so every word below it (old
outside words and fresh suffix words alike) outside the journal and the key buffer is kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section lw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB : BitVec 64}

/-- A triple over the arena with its bound raised to the entry heap pointer `Hc ≥ P0` holds over the arena. -/
theorem aqgd_jws_lower {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {Hc : BitVec 64} (le : P0.toNat ≤ Hc.toNat)
    (h : AQGD D B (JWS SP0 Hc FM G0 J C SKB) w Vn P Q RR p) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w Vn (fun L M G => P L M G ∧ HeapIs G Hc) Q RR p := by
  intro F s code dom aw sl H hH ⟨pre,hc⟩
  unfold GIs at hH; subst hH
  have awH : JWS SP0 Hc FM G0 J C SKB s.globals := ⟨⟨(aw_raise aw.1.1 hc).1,aw.1.2⟩,aw.2⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom awH sl _ rfl pre
  exact ⟨m,fun cont => let x := a cont; ⟨⟨(aw_lower x.1.1 le).1,x.1.2⟩,x.2⟩,n,r,c,b⟩

#print axioms aqgd_jws_lower
end lw

/-- Final suffix state: `PG` at some content heap pointer `Hb' ≥ Hg` and some journal counter. -/
def PZ (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (Lo Hg : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ Hb' Nj : BitVec 64, Hg.toNat ≤ Hb'.toNat ∧ PG n c T Out ko D B Excl Lo Hg Hb' Nj M0 M G

section pz
variable {D : BitVec 64 → Prop} {B : Bool}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Hb Nj Hg : BitVec 64} {M0 : Mem}

/-- The suffix state at the heap pointer `Hg` gives the final suffix state with the fresh words `[Hb, Hg)`. -/
theorem pz_of_pb {M : Mem} {G : GA} {kA kB : Fin n} (hAB : kA ≠ kB) (h : PB n c T Out ko D B Excl Hb Nj M0 M G)
    (hH : HeapIs G Hg) : PZ n c T Out ko D B Excl Hb Hg M0 M G :=
  ⟨Hg,Nj,le_refl _,pg_of_si (Lo := Hb) hAB h hH⟩

#print axioms pz_of_pb
end pz

section cl
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs Lo Hg : BitVec 64} {M0 : Mem}

/-- `clear_account_preserving_balance(e)` in the final suffix state; side facts `R` framed by the outside words of the
registry outside the journal and the key buffer, with a growing heap pointer. -/
theorem aqgd_call_clearAcct_pz {LP : GA → Prop} {R : Mem → GA → Prop} (e : ExpHOL 64)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) (hP0Lo : P0.toNat ≤ Lo.toNat)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      ∀ v, EV s e = some v → ∃ A : BitVec 64, v = .val (.word A))
    (hR : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), R M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x, OutX Out Lo Hg x → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M x) → R M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G)
      (fun L M G => (LP L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G) RR
      (.call (some (none,none)) (ofString "clear_account_preserving_balance") [e]) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T (OutX Out Lo Hg) (hpOf G0') M D B ko ∧ M = M0' ∧ HeapIs G (hpOf G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word (wordOf G0' (ofString "journal_n"))))) ∧
        HeapIs G (hpOf G0'))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      DAPost n c T (OutX Out Lo Hg) ko D B J C SKB (hpOf G0') M0' M' G')
    _ _ _ _ _ originalRuntimeCode_clearAccountPB_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨⟨_,Hb',Nj',hgb,⟨H1,hH1,hb1⟩,_,hn,_⟩,_⟩
    rw [hpOf_eq hH1,wordOf_eq hn]
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H1.toNat) (fun _ _ g aw ⟨_,hg⟩ => (aw_raise aw.1.1.1.1.1 hg).2) ?_
    intro p1
    exact aqgd_jwsbus (aqgd_jws_lower p1 (clearAcctPBT_aqgd (P0 := H1) (H0 := H1) (Out := OutX Out Lo Hg)
        (Nj := Nj') (M0 := M0') (w := w) ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 (le_refl _) jfit hwJ
        (by have := (hOutSafe w hOut).2; omega) (Or.inl hOut) hwS (fun x hx => Or.inl (hJO x hx))
        (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩) jsep K Pd NB hK0 hPd0 hNB0 safe
        (fun x hx => by
          rcases hx with ho | ⟨lo,hi⟩
          · exact ⟨(hOutSafe x ho).1,by have := (hOutSafe x ho).2; omega⟩
          · exact ⟨hWsP0 x (by omega),by omega⟩)
        hkoWs ECH hECH))
      (keepsBo_of_installed originalRuntimeCode_clearAccountPB_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_clearAccountPB_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_clearAccountPB_lookup (by decide))
  · intro F s values callee rs _ G hG ⟨⟨lp,Hb',Nj',_,⟨H1,hH1,hb1⟩,reg,hn,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    obtain ⟨A,rfl⟩ := hev s lp x ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_clearAccountPB_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    rw [hpOf_eq hH1,wordOf_eq hn]
    exact ⟨⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,regT_mono reg hb1,rfl,hH1,hn⟩,hH1⟩
  · intro L M G v M' G' ⟨⟨lp,Hb',Nj',hgb,⟨H1,hH1,hb1⟩,reg,hn,fr⟩,r⟩ ⟨H',hH',hle,reg',⟨Nj'',hn'⟩,fr'⟩
    rw [hpOf_eq hH1] at hle
    exact ⟨⟨lp,H',Nj'',by omega,⟨H',hH',le_refl _⟩,reg',hn',fun x ho hx =>
      (fr' x (Or.inl ho) (fun hj => hx (hJE x hj)) (fun hs => hx (hSE x hs))).trans (fr x ho hx)⟩,
      hR M M' G G' H1 H' r hH1 hH' hle (fun x ho hj hs => fr' x ho hj hs)⟩

#print axioms aqgd_call_clearAcct_pz

end cl
end InitECandidate.Runtime
