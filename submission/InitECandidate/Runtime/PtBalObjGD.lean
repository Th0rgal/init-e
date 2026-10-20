import InitECandidate.Runtime.PtMergeBodyGD
import InitECandidate.Runtime.PtBalLstGD
import InitECandidate.Runtime.OriginalBalCode
/-!
Owned-region block-access-list objects: `LstO E O Lh M` is a list header at `Lh` (`buf P, n N, cap Cp`, `N ≤ Cp`,
`0 < Cp`, 8-aligned) with header words and buffer `[P, P + E·Cp)` inside the owned region `O`, the buffer apart from the
header. The actual `e = lst_upsert_idx(l, esz, idx)` on such a list keeps it with `O` grown by the fresh heap
`[H, Hc)`, returns an element `[e, e + esz)` inside the grown region off the header, and changes no word below `H`
outside `O`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An owned-region list. -/
def LstO (E : BitVec 64) (O : BitVec 64 → Prop) (Lh : BitVec 64) (M : Mem) : Prop :=
  ∃ P N Cp : BitVec 64, LHd Lh P N Cp M ∧ N.toNat ≤ Cp.toNat ∧ 0 < Cp.toNat ∧ Lh.toNat % 8 = 0 ∧
    (∀ x, HdW Lh x → O x) ∧
    ∀ x : BitVec 64, P.toNat ≤ x.toNat → x.toNat < P.toNat + E.toNat * Cp.toNat → O x ∧ ¬ HdW Lh x

section lo
variable {E Lh : BitVec 64} {O O' : BitVec 64 → Prop} {M M' : Mem}

theorem lstO_sub (h : LstO E O Lh M) (sub : ∀ x, O x → O' x) : LstO E O' Lh M :=
  let ⟨P,N,Cp,hd,a,b,c,hh,hb⟩ := h
  ⟨P,N,Cp,hd,a,b,c,fun x hx => sub x (hh x hx),fun x l u => let ⟨o,n⟩ := hb x l u; ⟨sub x o,n⟩⟩

theorem lstO_frame (h : LstO E O Lh M) (keep : ∀ x, O x → M' x = M x) : LstO E O Lh M' := by
  obtain ⟨P,N,Cp,⟨h0,h8,h16⟩,a,b,c,hh,hb⟩ := h
  refine ⟨P,N,Cp,⟨?_,?_,?_⟩,a,b,c,hh,hb⟩
  · rw [keep _ (hh _ (Or.inl rfl))]; exact h0
  · rw [keep _ (hh _ (Or.inr (Or.inl rfl)))]; exact h8
  · rw [keep _ (hh _ (Or.inr (Or.inr rfl)))]; exact h16
end lo

/-- An interval all of whose words lie below `H` ends at or below `H`. -/
theorem buf_le {P K H : Nat} (hP : P < 2 ^ 64) (hH : H < 2 ^ 64) (hK : 0 < K)
    (h : ∀ x : BitVec 64, P ≤ x.toNat → x.toNat < P + K → x.toNat < H) : P + K ≤ H := by
  by_contra hc
  have := h (BitVec.ofNat 64 (max P H)) (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
  rw [BitVec.toNat_ofNat] at this; omega

/-- Element facts of an owned list. -/
theorem elem_in {P E Cn Nn j S : Nat} (hj : j < Nn) (hN : Nn ≤ Cn) (hS : S = P + j * E) :
    ∀ x : Nat, S ≤ x → x < S + E → P ≤ x ∧ x < P + E * Cn := by
  intro x h1 h2
  have m : (j + 1) * E ≤ Cn * E := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at m
  rw [Nat.mul_comm E Cn]
  constructor <;> omega

section lu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `var 1 name = lst_upsert_idx(el, eE, eI)` on an owned list. -/
theorem aqgd_decCall_lstUpsert_o {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS)
    (el eE eI : ExpHOL 64) {cont : ProgHOL 64} (Lh E I : BitVec 64) (O : BitVec 64 → Prop) (H Nj : BitVec 64)
    (M1 : Mem) (G1 : GA) (lo : LstO E O Lh M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hO : ∀ x, O x → x.toNat < H.toNat) (hwO : ¬ O w) (hwH : w.toNat < H.toNat) (hE1 : 1 ≤ E.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [el,eE,eI] =
        some [.val (.word Lh),.val (.word E),.val (.word I)])
    (hres : ∀ (L : GA) (S Hc : BitVec 64) (M' : Mem) (G' : GA), LP L → HeapIs G' Hc → H.toNat ≤ Hc.toNat →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) →
      LstO E (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) Lh M' →
      (∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + E.toNat →
        (O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW Lh x) →
      (∀ x, x.toNat < H.toNat → ¬ O x → M' x = M1 x) →
      Pc (L.update (name,.val (.word S))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "lst_upsert_idx") [el,eE,eI] cont) := by
  obtain ⟨P,N,Cp,hd,hNC,hC0,al,hHd,hBuf⟩ := lo
  have hHl : H.toNat < 2 ^ 64 := H.isLt
  have hCE : 0 < E.toNat * Cp.toNat := Nat.mul_pos (by omega) hC0
  have hbuf : P.toNat + E.toNat * Cp.toNat ≤ H.toNat :=
    buf_le P.isLt hHl hCE (fun x l u => hO x (hBuf x l u).1)
  have h16 : (Lh + 16#64).toNat < H.toNat := hO _ (hHd _ (Or.inr (Or.inr rfl)))
  have h0 : Lh.toNat < H.toNat := hO Lh (hHd Lh (Or.inl rfl))
  refine aqgd_decCallSpecD (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (LUPost Lh E P N Cp H M0' G0' v M' G' ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_lstUpsertIdx_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1 ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
      (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by
        rw [hg] at aw; exact ⟨aw.2,(jws_heap_facts aw.1.1.1 hH1).2.1,(jws_heap_facts aw.1.1.1 hH1).2.2⟩) ?_
    intro ⟨hsc,hHE,hal⟩
    have e16 : (Lh + 16#64).toNat = Lh.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
    have hsz : E.toNat * Cp.toNat * 2 < 2 ^ 64 := by omega
    have hwh : ¬ HdW Lh w := fun h => hwO (hHd w h)
    have hwB : ¬ (P.toNat ≤ w.toNat ∧ w.toNat < P.toNat + E.toNat * Cp.toNat) := fun ⟨a,b⟩ => hwO (hBuf w a b).1
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)] L ∧ M = M1 ∧
        HeapIs G H) ∧ G = G1) ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; rw [hG]; exact ⟨⟨⟨⟨lk,hM,by rw [← hG]; rw [hG]; exact hH1⟩,rfl⟩,hsc⟩,
        by rw [← hG]; exact jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstUpsertIdx_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstUpsertIdx_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)] L ∧ M = M1 ∧ HeapIs G H) ∧
        G = G1) ∧ ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstUpsertIdx_lookup (by decide))
        (lstUpsertIdx_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
          (SKB := SKB) (Nj := Nj) (w := w) Lh E I P N Cp H M1 G1 (by omega) hwH hwh hd hNC hC0 hE1 hbuf hsz hwB
          (fun x l u => (hBuf x l u).2)))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_three_word_lookup _ _ (ofString "l") (ofString "esz") (ofString "idx") _ _ _ _ (by decide) (by decide)
      (by decide) originalRuntimeCode_lstUpsertIdx_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,by rw [hG1]; exact hn1⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨⟨⟨_,S,Pn,Nn,Cn,Hc,ev,hd',hHc,le,hNn,hCn,hPn,⟨j,hj,hS⟩,old,_,fr⟩,_⟩,hn'⟩ _
    subst ev hM
    have bufN : ∀ x : BitVec 64, Pn.toNat ≤ x.toNat → x.toNat < Pn.toNat + E.toNat * Cn.toNat →
        (O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat)) ∧ ¬ HdW Lh x := by
      intro x l u
      rcases old with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact ⟨Or.inl (hBuf x l u).1,(hBuf x l u).2⟩
      · refine ⟨Or.inr ⟨by omega,by omega⟩,fun h => ?_⟩
        have := hO x (hHd x h); omega
    refine hres L S Hc M' G' lp hHc le hn' ⟨Pn,Nn,Cn,hd',hNn,hCn,al,fun x h => Or.inl (hHd x h),bufN⟩
      (fun x l u => bufN x (elem_in hj hNn hS x.toNat l u).1 (elem_in hj hNn hS x.toNat l u).2) ?_
    intro x hx ho
    refine fr x hx (fun h => ho (hHd x h)) (fun e => ?_)
    rw [e] at hx ho
    have hin := elem_in hj hNn hS S.toNat (le_refl _) (by omega)
    rcases bufN S hin.1 hin.2 with ⟨h | ⟨h,_⟩,_⟩
    · exact ho h
    · omega

#print axioms aqgd_decCall_lstUpsert_o
end lu
end InitECandidate.Runtime
