import InitECandidate.Runtime.PtSufDGD
/-!
The actual `lst_upsert_idx(l, esz, idx)` (whole-memory form over the pinned-journal arena) on a valid list header at
`Lh` (`buf P, n N, cap Cp`): the scan reads the entries only; it returns an entry `S = Pn + j·esz` (`j < Nn`) of the
resulting header `buf Pn, n Nn, cap Cn` — an existing entry (nothing written), or the new slot of `lst_push` with
`idx` stored at it. Every word below the entry heap pointer `H` other than the three header words and `S` is kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Postcondition of `lst_upsert_idx`. -/
def LUPost (Lh E P N Cp H : BitVec 64) (M0 : Mem) (Gk : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) : Prop :=
  OnlyHeap Gk G' ∧ ∃ S Pn Nn Cn Hc : BitVec 64, v = .val (.word S) ∧ LHd Lh Pn Nn Cn M' ∧ HeapIs G' Hc ∧
    H.toNat ≤ Hc.toNat ∧ Nn.toNat ≤ Cn.toNat ∧ 0 < Cn.toNat ∧ Pn.toNat + E.toNat * Cn.toNat ≤ Hc.toNat ∧
    (∃ j : BitVec 64, j.toNat < Nn.toNat ∧ S.toNat = Pn.toNat + j.toNat * E.toNat) ∧
    ((Pn = P ∧ Cn = Cp) ∨ (H.toNat ≤ Pn.toNat ∧ Cn.toNat = 2 * Cp.toNat)) ∧
    (Nn = N ∨ Nn.toNat = N.toNat + 1) ∧ ∀ x, x.toNat < H.toNat → ¬ HdW Lh x → x ≠ S → M' x = M0 x

section lu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- Locals of `lst_upsert_idx` during the scan. -/
def luPs (Lh E I N P Iv : BitVec 64) : List (MlS × BitVec 64) :=
  [(ofString "i",Iv),(ofString "p",P),(ofString "n",N),(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)]

/-- The push tail of `lst_upsert_idx`: `e = lst_push(l, esz); st e, idx; return e`. -/
theorem luPushTail {ps : List (MlS × BitVec 64)} (Lh E I P N Cp H : BitVec 64) (M0 : Mem) (Gk : GA)
    (hps : ∀ p ∈ [(ofString "l",Lh),(ofString "esz",E),(ofString "idx",I)], p ∈ ps)
    (hpsE : ∀ p ∈ ps, p.1 ≠ ofString "e")
    (hL : Lh.toNat + 24 ≤ H.toNat) (hw : w.toNat < H.toNat) (hwh : ¬ HdW Lh w)
    (hd : LHd Lh P N Cp M0) (hNC : N.toNat ≤ Cp.toNat) (hC0 : 0 < Cp.toNat) (hE1 : 1 ≤ E.toNat)
    (hbuf : P.toNat + E.toNat * Cp.toNat ≤ H.toNat) (hsz : E.toNat * Cp.toNat * 2 < 2 ^ 64)
    (hwB : ¬ (P.toNat ≤ w.toNat ∧ w.toNat < P.toNat + E.toNat * Cp.toNat))
    (hbH : ∀ x : BitVec 64, P.toNat ≤ x.toNat → x.toNat < P.toNat + E.toNat * Cp.toNat → ¬ HdW Lh x) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => (LK ps L ∧ M = M0 ∧ HeapIs G H) ∧ G = Gk) (fun _ _ _ => False) (LUPost Lh E P N Cp H M0 Gk)
      (.decCall (ofString "e") .one (ofString "lst_push") [.var .local (ofString "l"),.var .local (ofString "esz")]
        (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx"))) (.return (.var .local (ofString "e"))))) := by
  have hHl : H.toNat < 2 ^ 64 := H.isLt
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧ HeapIs G (hpOf G0')) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      LPPost Lh E P N Cp (hpOf G0') M0' G0' v M' G')
    (Pc := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64, (LK ((ofString "e",q.1 + N * E) :: ps) L ∧
      LHd Lh q.1 (N + 1#64) q.2.1 M ∧ HeapIs G q.2.2 ∧ OnlyHeap Gk G ∧
      ∀ x, x.toNat < H.toNat → ¬ HdW Lh x → M x = M0 x) ∧
      (H.toNat ≤ q.2.2.toNat ∧ N.toNat < q.2.1.toNat ∧ q.1.toNat + E.toNat * q.2.1.toNat ≤ q.2.2.toNat ∧
        ((q.1 = P ∧ q.2.1 = Cp) ∨ (H.toNat ≤ q.1.toNat ∧ q.2.1.toNat = 2 * Cp.toNat))))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_lstPush_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 M0' G0' ⟨⟨_,hM,hH⟩,hG⟩
    rw [hG] at hH ⊢
    rw [hpOf_eq hH]
    exact aqgd_conseq (lstPush_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
      (SKB := SKB) (Nj := Nj) (w := w) Lh E P N Cp H M0' Gk hL hw hwh (by rw [hM]; exact hd) hNC hC0 hE1 hbuf hsz)
      (fun L M G ⟨⟨lk,hM',hH'⟩,hG'⟩ => ⟨⟨lk,hM',hH'⟩,hG'⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG ⟨⟨lk,_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,lk (ofString "l",Lh) (hps _ (by simp)),lk (ofString "esz",E) (hps _ (by simp))]
      at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_lstPush_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨fun p hp => ?_,rfl,by rw [hpOf_eq hH]; exact hH⟩,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨⟨lk,hM,hH⟩,hG⟩ post _
    subst hM hG
    rw [hpOf_eq hH] at post
    obtain ⟨fr,oh,Pn,Cn,Hc,ev,hd',hHc,le,lt,hbuf',alt⟩ := post
    subst ev
    exact ⟨(Pn,Cn,Hc),⟨lk_update' lk _ _ hpsE,hd',hHc,oh,fr⟩,le,lt,hbuf',alt⟩
  refine aqgd_ex (fun q => aqgd_purePre (fun ⟨le,lt,hbuf',alt⟩ => ?_))
  obtain ⟨Pn,Cn,Hc⟩ := q
  dsimp only at le lt hbuf' alt ⊢
  have hHc : Hc.toNat < 2 ^ 64 := Hc.isLt
  have sa := slot_arith (E := E.toNat) lt
  have eNE : (N * E).toNat = N.toNat * E.toNat := mul_nat (by omega)
  have eS : (Pn + N * E).toNat = Pn.toNat + N.toNat * E.toNat := by
    rw [BitVec.toNat_add,eNE]; exact Nat.mod_eq_of_lt (by omega)
  have eN1 : (N + 1#64).toNat = N.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have hSloc : ¬ HdW Lh (Pn + N * E) ∧ w ≠ Pn + N * E := by
    rcases alt with ⟨rfl,rfl⟩ | ⟨hp,_⟩
    · refine ⟨hbH _ (by omega) (by rw [eS]; omega),fun e => hwB ?_⟩
      rw [e,eS]; constructor <;> omega
    · refine ⟨fun h => ?_,fun e => ?_⟩
      · have := hdw_lt hL h; omega
      · rw [e] at hw; omega
  refine aqgd_seq (Q := fun L M G => LK ((ofString "e",Pn + N * E) :: ps) L ∧ LHd Lh Pn (N + 1#64) Cn M ∧
      HeapIs G Hc ∧ OnlyHeap Gk G ∧ ∀ x, x.toNat < H.toNat → ¬ HdW Lh x → x ≠ Pn + N * E → M x = M0 x)
    (aqgd_storeD _ _ (fun s G _ _ hG ⟨lk,hd',hHc',oh,fr⟩ _ => ?_)
      (fun s x _ _ _ _ ⟨lk,_⟩ _ ev => by
        simp [EV,evalHOLExact,lk (ofString "idx",I) (List.mem_cons_of_mem _ (hps _ (by simp)))] at ev
        exact ⟨I,ev.symm⟩))
    (aqgd_return _ (fun s v G _ hG ⟨lk,hd',hHc',oh,fr⟩ _ ev => ?_))
  · unfold GIs at hG; subst hG
    refine ⟨Pn + N * E,by simp [EV,evalHOLExact,lk (ofString "e",Pn + N * E) (by simp)],hSloc.2,fun y _ => ?_⟩
    refine ⟨lk,?_,hHc',oh,fun x hx hh hne => by simp [hne]; exact fr x hx hh⟩
    obtain ⟨d0,d8,d16⟩ := hd'
    have n0 : Lh ≠ Pn + N * E := fun e => hSloc.1 (e ▸ Or.inl rfl)
    have n8 : Lh + 8#64 ≠ Pn + N * E := fun e => hSloc.1 (e ▸ Or.inr (Or.inl rfl))
    have n16 : Lh + 16#64 ≠ Pn + N * E := fun e => hSloc.1 (e ▸ Or.inr (Or.inr rfl))
    exact ⟨by simp [n0]; exact d0,by simp [n8]; exact d8,by simp [n16]; exact d16⟩
  · unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,lk (ofString "e",Pn + N * E) (by simp)] at ev
    subst ev
    exact ⟨oh,Pn + N * E,Pn,N + 1#64,Cn,Hc,rfl,hd',hHc',le,by omega,by omega,hbuf',⟨N,by omega,eS⟩,alt,
      Or.inr eN1,fr⟩

end lu
end InitECandidate.Runtime
