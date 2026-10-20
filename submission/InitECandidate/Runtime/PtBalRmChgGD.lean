import InitECandidate.Runtime.PtBalRemoveGD
/-!
The actual `bal_remove_change(addr, which, esz, idx)`: look the account up in `bal_accounts`; when present, remove the
transaction index from the record's change list at field offset `which` (balance 16/40, nonce 24/16, code 32/24). The
block-access-list state steps from the entry (same live accounts and heap pointer, memory changed inside the list).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The record field offset and element size of one of the three change lists. -/
def ChgSel (W E : BitVec 64) : Prop :=
  (W = 16#64 ∧ E = 40#64) ∨ (W = 24#64 ∧ E = 16#64) ∨ (W = 32#64 ∧ E = 24#64)

theorem chgSel_E {W E : BitVec 64} (h : ChgSel W E) : 1 ≤ E.toNat := by
  rcases h with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide

section ad
variable {D : BitVec 64 → Prop} {B : Bool}

/-- The change list selected by `(W, E)` in a valid owned record (field word owned too). -/
theorem adO_lstW {O : BitVec 64 → Prop} {ad H W E : BitVec 64} {M : Mem} (sel : ChgSel W E) (h : AdO D B O ad H M) :
    ∃ (l : BitVec 64) (R : BitVec 64 → Prop), M (ad + W) = .word l ∧ LstO E R l M ∧ (∀ x, R x → O x) ∧
      O (ad + W) ∧
      ∀ (M' : Mem) (H' : BitVec 64), H.toNat ≤ H'.toNat →
        LstO E (fun x => R x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) l M' →
        (∀ x, x.toNat < H.toNat → ¬ R x → M' x = M x) → (∀ x, O x → x.toNat < H.toNat) →
        AdO D B (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ad H' M' := by
  have rw' : ∀ x, RecW ad x → O x := fun x hx => by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hrw,_,_,_,_,_,_,_,inO⟩ := h
    exact inO .recw trivial x (hrw x hx)
  rcases sel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · obtain ⟨l,R,c,lo,hR,u⟩ := adO_lst16 h
    exact ⟨l,R,c,lo,hR,rw' _ (Or.inr (Or.inr (Or.inl rfl))),u⟩
  · obtain ⟨l,R,c,lo,hR,u⟩ := adO_lst24 h
    exact ⟨l,R,c,lo,hR,rw' _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),u⟩
  · obtain ⟨l,R,c,lo,hR,u⟩ := adO_lst32 h
    exact ⟨l,R,c,lo,hR,rw' _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),u⟩

#print axioms adO_lstW
end ad

/-- Locals of `bal_remove_change`. -/
def RCL (A W E I : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "which") = some (.val (.word W)) ∧
  L.lookup (ofString "esz") = some (.val (.word E)) ∧ L.lookup (ofString "idx") = some (.val (.word I))

theorem rcl_upd {A W E I : BitVec 64} {L : GA} (h : RCL A W E I L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "addr" ≠ x) (h2 : ofString "which" ≠ x) (h3 : ofString "esz" ≠ x) (h4 : ofString "idx" ≠ x) :
    RCL A W E I (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2.1,by rw [lookup_update_ne' _ _ h4]; exact h.2.2.2⟩

section rc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `bal_remove_change` body. -/
theorem removeChange_aqgd (bk : BalKeep) (BA IA IS KB Ix A W E I : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (sel : ChgSel W E)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => RCL A W E I L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G)
      (sourceFunctionBody Guest.guestFn_bal_remove_change) := by
  refine aqgd_of_arenaFact (Φ := H.toNat ≤ 33806089496)
    (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact (jws_heap_facts aw.1.1.1 hH1).2.1) ?_
  intro hHE
  have gba := hB1.1
  obtain ⟨lba,Hl,rvba,hHl,klba,_,_⟩ := bw.1 .ba trivial
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_bal_remove_change,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aqgd_decCall_htabGet_b bk BA IA IS KB Ix (LP := RCL A W E I)
    (Pc := fun L M G => (RCL A W E I L ∧ ∃ p val : BitVec 64,
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ (p ≠ 0 → val ∈ ADs)) ∧
      M = M1 ∧ G = G1)
    (Qc := fun _ _ _ => False) (ofString "m") _ _ BA A Hl H lba ADs M1 G1 rvba hH1 hHl hB1 Dall (Or.inl klba) hK hKE ?_
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ hg ⟨la,_⟩
    have gb : s.globals.lookup (ofString "bal_accounts") = some (.val (.word BA)) := by rw [hg]; exact gba
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la,gb]
  · intro L p val la _ prop
    exact ⟨⟨rcl_upd la _ _ (by decide) (by decide) (by decide) (by decide),p,val,lookup_update_eq' _ _ _,prop⟩,rfl,rfl⟩
  refine aqgd_seq (Q := fun L M G => (RCL A W E I L ∧ ∃ p val : BitVec 64,
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ val ∈ ADs) ∧ M = M1 ∧ G = G1)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun L _ _ => ∃ p val : BitVec 64,
        L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ p ≠ 0)
      _ ?_ ?_ ?_) ?_
  · intro F s x H' _ _ ⟨⟨_,p,val,hm,_⟩,_,_⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ⟨p,val,hm,fun hp => ?_⟩⟩
    subst hp hx
    simp [EV,evalHOLExact,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
  · refine aqgd_return _ (fun s v H' _ hG ⟨⟨_,hM,hG1⟩,_⟩ _ ev => ?_)
    simp [EV,evalHOLExact] at ev
    subst ev
    unfold GIs at hG; subst hG
    rw [hM,hG1]
    exact ⟨rfl,balStep_refl bw hH1 hn1⟩
  · refine aqgd_conseq aqgd_skip (fun L M G ⟨⟨⟨lr,p,val,hm,prop⟩,hM,hG⟩,⟨p',val',hm',hp'⟩⟩ => ?_) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    rw [hm] at hm'
    simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,
      HolWordLab.word.injEq,and_true] at hm'
    obtain ⟨rfl,rfl⟩ := hm'
    exact ⟨⟨lr,p,val,hm,prop hp'⟩,hM,hG⟩
  refine aqgd_conseq (P := fun L M G => ∃ p val : BitVec 64, ((RCL A W E I L ∧
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)])) ∧ M = M1 ∧ G = G1) ∧ val ∈ ADs)
    (aqgd_ex (fun p => aqgd_ex (fun val => aqgd_pureE (fun had => ?_))))
    (fun L M G ⟨⟨lr,p,val,hm,had⟩,hM,hG⟩ => ⟨p,val,⟨⟨lr,hm⟩,hM,hG⟩,had⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have adv : AdO D B (Rg (.ad val)) val H M1 := bw.1 (.ad val) had
  have hbl := bw.2.2 (.ad val) had
  obtain ⟨l,R,cell,lo,hR,inW,upd⟩ := adO_lstW sel adv
  have hwO : ¬ R w := fun h => hwR (.ad val) had (hR w h)
  have hO : ∀ x, R x → x.toNat < H.toNat := fun x hx => hbl x (hR x hx)
  have dW : (val + W).toNat < 33806089496 := by have := hbl _ inW; omega
  refine aqgd_seq (aqgd_call_balListRemove (LP := fun L => RCL A W E I L ∧
      L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)])) _ _ _ l E I R H M1 G1 lo hwO hO hHE
    (chgSel_E sel) Dall ?_) ?_
  · intro F s hd hm _ ⟨⟨_,lw,le,li⟩,lm⟩
    have ea : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.rfield 1 (.var .local (ofString "m")),.var .local (ofString "which")]) =
          some (.val (.word (val + W))) := by
      simp [evalHOLExact,evalListHOLExact,lm,lw,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact,eval_load_word s _ _ l ea (by rw [hd]; exact Dall _ dW) (by rw [hm]; exact cell)]
    simp [evalHOLExact,le,li]
  refine aqgd_return _ (fun s v H'' _ hG ⟨_,hG',lo',fr⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  subst ev
  unfold GIs at hG; subst hG
  refine ⟨rfl,?_⟩
  rw [hG']
  exact balStep_upd bw (le_refl _) (fun _ h => h) (fun c hc x hx => Or.inl ⟨hc,hx⟩) (fun _ _ _ => rfl) (.ad val) had
    (le_refl _) (upd s.memory H (le_refl _) (lstO_sub lo' (fun x h => Or.inl h)) (fun x _ hx => fr x hx) hbl)
    (fun x _ hx => fr x (fun h => hx (hR x h))) hH1 hn1

#print axioms removeChange_aqgd
end rc
end InitECandidate.Runtime
