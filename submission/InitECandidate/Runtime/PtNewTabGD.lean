import InitECandidate.Runtime.PtSetGD
/-!
`name = htab_new(KL, Cp)` at the segment call site: the fresh table `Tt` (at or above the heap pointer `H` at the
call, hence at or above `Lo`) is valid (`TBf Tt Tt`), `SI` is kept, and a property `R0` framed below `H` becomes
`R1 Tt` (it may mention the new table base).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section nt
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

theorem aqgd_decCall_htabNew_si {LP LP' : GA → Prop} {R0 : Mem → GA → Prop} {R1 : BitVec 64 → Mem → GA → Prop}
    {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (KL Cp : BitVec 64) (b : Nat) {cont : ProgHOL 64}
    (pow : Cp.toNat = 2 ^ b) (fits : KL.toNat ≤ ((KL + 7#64) &&& (0#64 - 8#64)).toNat)
    (sdAl : ((KL + 7#64) &&& (0#64 - 8#64)).toNat % 8 = 0)
    (mulK : (Cp * ((KL + 7#64) &&& (0#64 - 8#64))).toNat = Cp.toNat * ((KL + 7#64) &&& (0#64 - 8#64)).toNat)
    (mul8 : (Cp * 8#64).toNat = Cp.toNat * 8) (hw : w.toNat < Lo.toNat)
    (hR : ∀ (M M' : Mem) (G G' : GA) (H H' Tt : BitVec 64), R0 M G → HeapIs G H → H.toNat ≤ Tt.toNat →
      HeapIs G' H' → Tt.toNat + 72 ≤ H'.toNat → (∀ x : BitVec 64, x.toNat < H.toNat → M' x = M x) → R1 Tt M' G')
    (hup : ∀ L v, LP L → LP' (L.update (name,v)))
    (hcont : ∀ Tt : BitVec 64, Lo.toNat ≤ Tt.toNat →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => ((LP' L ∧ L.lookup name = some (.val (.word Tt))) ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧
          TBf Tt Tt M G ∧ R1 Tt M G) Q RR cont)
    (hres : ∀ L M G L' M' G', (LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ R0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ R0 M G) Q2 RR
      (.decCall name .one (ofString "htab_new") [.const KL,.const Cp] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      LK [(ofString "cap",Cp),(ofString "key_len",KL)] L ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H : BitVec 64, HeapIs G0' H ∧ ((∃ Tt : BitVec 64, v = .val (.word Tt) ∧ H.toNat ≤ Tt.toNat ∧
        (∀ x, x.toNat < H.toNat → M' x = M0' x) ∧ OnlyHeap G0' G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          Tt.toNat + 72 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M') ∧ ScrIs Sc G') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => ∃ Tt : BitVec 64, (((LP' L ∧ L.lookup name = some (.val (.word Tt))) ∧
      SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Tt Tt M G ∧ R1 Tt M G) ∧ Lo.toNat ≤ Tt.toNat)
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_
    (aqgd_exE (fun Tt => aqgd_pureE (fun le => hcont Tt le))) hres
  · intro L0 M0' G0' ⟨⟨_,⟨H,hH,le⟩,_,hn,_⟩,_⟩
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G0') (fun _ _ g aw ⟨_,_,hg⟩ => by subst hg; exact aw.2) ?_
    intro hsc
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_htabNew_lookup
      (by decide)) (htabNew_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) (w := w) KL Cp H (by omega) M0' G0'))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_htabNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_htabNew_lookup (by decide)) h1) ?_ (fun _ _ _ h => h.elim) ?_
    · intro L M G ⟨lk,hM,hG⟩
      subst hM hG
      exact ⟨⟨⟨⟨lk,rfl,hH⟩,rfl⟩,hsc⟩,hn⟩
    · intro v M' G' ⟨rr,hn'⟩
      exact ⟨H,hH,rr,hn'⟩
  · intro F s values callee rs _ H' hG _ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    have e := callee_eq originalRuntimeCode_htabNew_lookup lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨⟨lp,si⟩,r0⟩ ⟨H,hH,⟨⟨Tt,ev,hHT,fr,_,H',hH',hT,hE,nt⟩,_⟩,hn'⟩ _
    subst ev
    obtain ⟨H1,hH1,le1⟩ := si.1
    have e := heapIs_unique hH1 hH
    subst e
    exact ⟨Tt,⟨⟨⟨hup L _ lp,lookup_update_eq' _ _ _⟩,si_glob (si_mem si (fun x hx => fr x (by omega)))
      ⟨H',hH',by omega⟩ hn'⟩,⟨H',H',tabV_ofNew nt hT hE (le_refl _) pow fits sdAl mulK mul8,hH',le_refl _⟩,
      hR M M' G G' H1 H' Tt r0 hH1 hHT hH' hT fr⟩,by omega⟩

#print axioms aqgd_decCall_htabNew_si
end nt
end InitECandidate.Runtime
