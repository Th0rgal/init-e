import InitECandidate.Runtime.PtBalNonceGD
/-!
`bal_list_remove_idx(l, esz, idx)` on an owned list: the scan reads only; a found element is overwritten by the last
one (`memcpy`, whose byte window lies inside the buffer and off the header) and the count is decremented. The list stays
an owned list in its region and no word outside the region changes.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section mc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- The actual `memcpy(ed, es, en)` call: memory changes only inside the byte window of `[Dd, Dd + N)`. -/
theorem aqgd_call_memcpyW {LP : GA → Prop} (ed es en : ExpHOL 64) (Dd S N : BitVec 64) (M1 : Mem) (G1 : GA)
    (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin Dd N.toNat w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ed,es,en] =
        some [.val (.word Dd),.val (.word S),.val (.word N)]) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ G = G1 ∧ ∀ x, ¬ MWin Dd N.toNat x → M x = M1 x) RR
      (.call (some (none,none)) (ofString "memcpy") [ed,es,en]) := by
  refine aqgd_callSpecD (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧ L.lookup (ofString "src") = some (.val (.word S)) ∧
        L.lookup (ofString "n") = some (.val (.word N))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ MWin Dd N.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' _
    exact aqgd_conseq (aqgd_of_window (Pe := fun L _ => L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word N)))
      memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy) (by body_check Guest.guestFn_memcpy)
      (MWin Dd N.toNat) (fun s _ ⟨hd,hs,hn⟩ x hx => memcpy_body_window s Dd S N x hd hs hn small hx) out M0' G0')
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_three_word_lookup _ _ (ofString "dst") (ofString "src") (ofString "n") _ _ _ _ (by decide) (by decide)
      (by decide) originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨eG,fr⟩
    exact ⟨lp,by rw [eG,hG],fun x hx => by rw [fr x hx,hM]⟩

#print axioms aqgd_call_memcpyW
end mc

/-- The byte window of a buffer element lies in the list's region and off its header. -/
theorem mwin_lst {E Lh P Cp Iv x : BitVec 64} {O : BitVec 64 → Prop} (al : Lh.toNat + 24 ≤ P.toNat)
    (hBuf : ∀ x : BitVec 64, P.toNat ≤ x.toNat → x.toNat < P.toNat + E.toNat * Cp.toNat →
      O x ∧ ¬ HdW Lh x ∧ O (panByteAlignHOL x))
    (hI : Iv.toNat < Cp.toNat) (fit : P.toNat + E.toNat * Cp.toNat < 2 ^ 64)
    (eD : (P + Iv * E).toNat = P.toNat + Iv.toNat * E.toNat) (hx : MWin (P + Iv * E) E.toNat x) :
    O x ∧ ¬ HdW Lh x := by
  have m : (Iv.toNat + 1) * E.toNat ≤ Cp.toNat * E.toNat := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul,Nat.mul_comm Cp.toNat] at m
  obtain ⟨j,hj,h⟩ := hx
  have ej : (P + Iv * E + BitVec.ofNat 64 j).toNat = P.toNat + Iv.toNat * E.toNat + j := by
    rw [BitVec.toNat_add,eD]; simp; omega
  have inB := hBuf (P + Iv * E + BitVec.ofNat 64 j) (by rw [ej]; omega) (by rw [ej]; omega)
  rcases h with rfl | rfl
  · exact ⟨inB.1,inB.2.1⟩
  · refine ⟨inB.2.2,fun hh => ?_⟩
    have ba : (panByteAlignHOL (P + Iv * E + BitVec.ofNat 64 j)).toNat + 8 > P.toNat + Iv.toNat * E.toNat + j := by
      rw [panByteAlign_toNat64,ej]
      have := Nat.mod_add_div (P.toNat + Iv.toNat * E.toNat + j) 8
      have := Nat.mod_lt (P.toNat + Iv.toNat * E.toNat + j) (by decide : 0 < 8)
      omega
    have e8 : (Lh + 8#64).toNat = Lh.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    have e16 : (Lh + 16#64).toNat = Lh.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
    rcases hh with e | e | e <;> rw [e] at ba
    · omega
    · rw [e8] at ba; omega
    · rw [e16] at ba; omega

#print axioms mwin_lst
section rm
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}

/-- The actual `bal_list_remove_idx(l, esz, idx)` body on an owned list. -/
theorem balListRemove_aqgd (Lh E I : BitVec 64) (O : BitVec 64 → Prop) (Hb : BitVec 64) (M0 : Mem) (Gk : GA)
    (lo : LstO E O Lh M0) (hwO : ¬ O w) (hO : ∀ x, O x → x.toNat < Hb.toNat) (hHb : Hb.toNat ≤ 33806089496)
    (hE1 : 1 ≤ E.toNat) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B A w (fun _ => False)
      (fun L M G => (L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I))) ∧ M = M0 ∧ G = Gk) (fun _ _ _ => False)
      (fun _ M G => G = Gk ∧ LstO E O Lh M ∧ ∀ x, ¬ O x → M x = M0 x)
      (sourceFunctionBody Guest.guestFn_bal_list_remove_idx) := by
  have lo' := lo
  obtain ⟨P,N,Cp,⟨hd0,hd8,hd16⟩,hNC,hC0,al,hHd,hBuf⟩ := lo'
  have hCE : 0 < E.toNat * Cp.toNat := Nat.mul_pos (by omega) hC0
  have hbuf : P.toNat + E.toNat * Cp.toNat ≤ Hb.toNat := buf_le P.isLt Hb.isLt hCE (fun x l u => hO x (hBuf x l u).1)
  have hEle : E.toNat ≤ E.toNat * Cp.toNat := Nat.le_mul_of_pos_right _ hC0
  have hCle : Cp.toNat ≤ E.toNat * Cp.toNat := Nat.le_mul_of_pos_left _ (by omega)
  have hN63 : N.toNat < 2 ^ 63 := by omega
  have h16 : (Lh + 16#64).toNat < Hb.toNat := hO _ (hHd _ (Or.inr (Or.inr rfl)))
  have h0 : Lh.toNat < Hb.toNat := hO Lh (hHd Lh (Or.inl rfl))
  have e8 : (Lh + 8#64).toNat = Lh.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have a0 : Lh + 0#64 = Lh := by simp
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_bal_list_remove_idx,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aqgd_decD (Pb := fun L M G => ((L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I))) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧ M = M0 ∧ G = Gk)
    (Qb := fun _ _ _ => False) (ofString "n") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨ll,le,li⟩,hM,hG⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "l") Lh 8#64 N (by simp [evalHOLExact,ll])
      (by rw [dom.2.1]; exact Dall _ (by omega)) (by rw [hM]; exact hd8)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact le,
      by rw [lookup_update_ne' _ _ (by decide)]; exact li⟩,lookup_update_eq' _ _ _⟩,hM,hG⟩
  refine aqgd_decD (Pb := fun L M G => (L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        L.lookup (ofString "p") = some (.val (.word P))) ∧ M = M0 ∧ G = Gk)
    (Qb := fun _ _ _ => False) (ofString "p") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨⟨ll,le,li⟩,ln⟩,hM,hG⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "l") Lh 0#64 P (by simp [evalHOLExact,ll])
      (by rw [dom.2.1,a0]; exact Dall _ (by omega)) (by rw [hM,a0]; exact hd0)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact le,
      by rw [lookup_update_ne' _ _ (by decide)]; exact li,by rw [lookup_update_ne' _ _ (by decide)]; exact ln,
      lookup_update_eq' _ _ _⟩,hM,hG⟩
  refine aqgd_decD (Pb := fun L M G => ((L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        L.lookup (ofString "p") = some (.val (.word P))) ∧ ∃ Iv : BitVec 64, L.lookup (ofString "i") = some (.val (.word Iv)) ∧
      Iv.toNat ≤ N.toNat) ∧ M = M0 ∧ G = Gk)
    (Qb := fun _ _ _ => False) (ofString "i") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ dom _ ⟨⟨ll,le,li,ln,lp⟩,hM,hG⟩ _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact le,
      by rw [lookup_update_ne' _ _ (by decide)]; exact li,by rw [lookup_update_ne' _ _ (by decide)]; exact ln,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lp⟩,0#64,lookup_update_eq' _ _ _,by simp⟩,hM,hG⟩
  refine aqgd_seq (Q := fun L M G => M = M0 ∧ G = Gk) ?_
    (aqgd_return _ (fun s v H'' _ hG ⟨hM,hG'⟩ _ _ => by
      unfold GIs at hG; subst hG; rw [hM]; exact ⟨hG',lo,fun _ _ => rfl⟩))
  refine aqgd_conseq (aqgd_whileE (C := fun L _ _ => ∃ Iv : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word Iv)) ∧ Iv.toNat < N.toNat) (E := fun _ _ _ => True)
      (Qb := fun _ _ _ => False) _ ?_ (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd ?_))
    (fun _ _ _ h => h) (fun L M G h => h.elim (fun ⟨⟨_,hM,hG⟩,_⟩ => ⟨hM,hG⟩) False.elim) (fun _ _ _ h => h)
  · intro F s x _ _ ⟨⟨⟨_,_,_,ln,_⟩,Iv,hi,hle⟩,_,_⟩ _ ev hx
    simp [EV,evalHOLExact,hi,ln,slt_small (b := N) (show Iv.toNat < 2 ^ 63 by omega)] at ev
    split at ev
    · rename_i h; exact ⟨Iv,hi,h.2⟩
    · exact absurd ev.symm hx
  refine aqgd_conseq (P := fun L M G => ∃ Iv : BitVec 64, (((L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧
      M = M0 ∧ G = Gk) ∧ Iv.toNat < N.toNat) (aqgd_ex (fun Iv => aqgd_pureE (fun hlt => ?_)))
    (fun L M G ⟨⟨⟨loc,_⟩,hM,hG⟩,Iv,hi,hlt⟩ => ⟨Iv,⟨⟨loc,hi⟩,hM,hG⟩,hlt⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have eD : (P + Iv * E).toNat = P.toNat + Iv.toNat * E.toNat := by
    have : Iv.toNat * E.toNat ≤ E.toNat * Cp.toNat := by
      rw [Nat.mul_comm E.toNat]; exact Nat.mul_le_mul (show Iv.toNat ≤ Cp.toNat by omega) (le_refl _)
    exact itm_toNat_add_mul P Iv E (by omega)
  have hIC : Iv.toNat < Cp.toNat := by omega
  have win : ∀ x, MWin (P + Iv * E) E.toNat x → O x ∧ ¬ HdW Lh x := fun x hx =>
    mwin_lst al hBuf hIC (by omega) eD hx
  refine aqgd_seq (Q := fun L M G => ((L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ M = M0 ∧ G = Gk)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · refine aqgd_seq (Q := fun L M G => ((L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ G = Gk ∧
        ∀ x, ¬ MWin (P + Iv * E) E.toNat x → M x = M0 x)
      (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
        (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
        (aqgd_conseq (aqgd_call_memcpyW (LP := fun L => (L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
        L.lookup (ofString "p") = some (.val (.word P))) ∧ L.lookup (ofString "i") = some (.val (.word Iv))) _ _ _
          (P + Iv * E) (P + (N - 1#64) * E) E M0 Gk (by omega) (fun h => hwO (win w h).1) ?_)
          (fun _ _ _ h => h.1.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        (aqgd_conseq aqgd_skip (fun _ _ _ h => ⟨h.1.1.1,h.1.1.2.2,fun x _ => by rw [h.1.1.2.1]⟩) (fun _ _ _ h => h)
          (fun _ _ _ h => h))) ?_
    · intro F s _ _ _ ⟨⟨_,le,_,ln,lp⟩,hi⟩
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact,evalHOLExact,le,ln,lp,hi,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
    refine aqgd_seq (aqgd_storeW (Q := fun L M G => G = Gk ∧ M (Lh + 8#64) = .word (N - 1#64) ∧
        ∀ x, ¬ MWin (P + Iv * E) E.toNat x → x ≠ Lh + 8#64 → M x = M0 x) _ _
      (fun s _ _ ⟨⟨⟨ll,_,_,ln,_⟩,_⟩,hG,fr⟩ => ⟨Lh + 8#64,N - 1#64,by simp [EV,evalHOLExact,evalListHOLExact,ll,
        wordOpHOL,wordOp,valueIsWord,valueWord],by simp [EV,evalHOLExact,evalListHOLExact,ln,wordOpHOL,wordOp,
        valueIsWord,valueWord],fun e => hwO (e ▸ hHd _ (Or.inr (Or.inl rfl))),hG,by simp,
        fun x hx hne => by simp only [if_neg hne]; exact fr x hx⟩)) ?_
    refine aqgd_return _ (fun s v H'' _ hG ⟨hG',c8,fr⟩ _ _ => ?_)
    unfold GIs at hG; subst hG
    have n0 : Lh ≠ Lh + 8#64 := fun e => by have := congrArg BitVec.toNat e; rw [e8] at this; omega
    have n16 : Lh + 16#64 ≠ Lh + 8#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [e8,show (Lh + 16#64).toNat = Lh.toNat + 16 by
        rw [BitVec.toNat_add]; simp; omega] at this; omega
    have nw : ∀ x, HdW Lh x → ¬ MWin (P + Iv * E) E.toNat x := fun x hx hw' => (win x hw').2 hx
    have eN : (N - 1#64).toNat = N.toNat - 1 := by
      rw [BitVec.toNat_sub]; simp; omega
    refine ⟨hG',⟨P,N - 1#64,Cp,⟨by rw [fr _ (nw _ (Or.inl rfl)) n0]; exact hd0,c8,
      by rw [fr _ (nw _ (Or.inr (Or.inr rfl))) n16]; exact hd16⟩,by rw [eN]; omega,hC0,al,hHd,hBuf⟩,
      fun x hx => fr x (fun hw' => hx (win x hw').1) (fun e => hx (e ▸ hHd _ (Or.inr (Or.inl rfl))))⟩
  · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨ll,le,li,ln,lp⟩,hi⟩,hM,hG⟩ _ ev => ?_)
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e1 : (Iv + 1#64).toNat = Iv.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    exact ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ll,by rw [lookup_update_ne' _ _ (by decide)]; exact le,
      by rw [lookup_update_ne' _ _ (by decide)]; exact li,by rw [lookup_update_ne' _ _ (by decide)]; exact ln,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lp⟩,Iv + 1#64,lookup_update_eq' _ _ _,by rw [e1]; omega⟩,hM,hG⟩

#print axioms balListRemove_aqgd
end rm
section rc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- The actual `bal_list_remove_idx(el, eE, ei)` call statement on an owned list: globals unchanged, the list stays
owned in `O`, memory outside `O` unchanged. -/
theorem aqgd_call_balListRemove {LP : GA → Prop} (el eE ei : ExpHOL 64) (Lh E I : BitVec 64) (O : BitVec 64 → Prop)
    (Hb : BitVec 64) (M1 : Mem) (G1 : GA) (lo : LstO E O Lh M1) (hwO : ¬ O w) (hO : ∀ x, O x → x.toNat < Hb.toNat)
    (hHb : Hb.toNat ≤ 33806089496) (hE1 : 1 ≤ E.toNat) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [el,eE,ei] =
        some [.val (.word Lh),.val (.word E),.val (.word I)]) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ G = G1 ∧ LstO E O Lh M ∧ ∀ x, ¬ O x → M x = M1 x) RR
      (.call (some (none,none)) (ofString "bal_list_remove_idx") [el,eE,ei]) := by
  refine aqgd_callSpecD (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "l") = some (.val (.word Lh)) ∧ L.lookup (ofString "esz") = some (.val (.word E)) ∧
        L.lookup (ofString "idx") = some (.val (.word I))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ LstO E O Lh M' ∧ ∀ x, ¬ O x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_balListRemoveIdx_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    exact aqgd_conseq (balListRemove_aqgd Lh E I O Hb M1 G1 lo hwO hO hHb hE1 Dall)
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_three_word_lookup _ _ (ofString "l") (ofString "esz") (ofString "idx") _ _ _ _ (by decide) (by decide)
      (by decide) originalRuntimeCode_balListRemoveIdx_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨eG,lo',fr⟩
    subst hM hG
    exact ⟨lp,eG,lo',fr⟩

#print axioms aqgd_call_balListRemove
end rc
end InitECandidate.Runtime
