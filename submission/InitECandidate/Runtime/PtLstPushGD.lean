import InitECandidate.Runtime.PtLstGD
/-!
The actual `lst_push(l, esz)` (whole-memory form over the pinned-journal arena) on a valid list header at `Lh`
(`buf P, n N, cap Cp` with `0 < Cp`, `N ≤ Cp`, buffer `[P, P + esz·Cp)` and header below the entry heap pointer `H`):
it returns the slot `Pn + N·esz` of the new header `buf Pn, n N + 1, cap Cn` (`N < Cn`, `[Pn, Pn + esz·Cn)` below the
exit heap pointer); either the buffer is kept (`Pn = P`, `Cn = Cp`) or it moved to a fresh block at or above `H`
(`Cn = 2 Cp`). Every word below `H` other than the three header words is kept, and only `heap_ptr` changes.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The three header words of a list at `Lh`. -/
def HdW (Lh x : BitVec 64) : Prop := x = Lh ∨ x = Lh + 8#64 ∨ x = Lh + 16#64

/-- A list header `buf P, n N, cap Cp` at `Lh`. -/
def LHd (Lh P N Cp : BitVec 64) (M : Mem) : Prop :=
  M Lh = .word P ∧ M (Lh + 8#64) = .word N ∧ M (Lh + 16#64) = .word Cp

section lp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- Join state after the growth branch of `lst_push`. -/
def LPJ (Lh E P N Cp H Nv : BitVec 64) (M0 : Mem) (Gk : GA) (L : GA) (M : Mem) (G : GA) : Prop :=
  LK [(ofString "cap",Cp),(ofString "n",N),(ofString "l",Lh),(ofString "esz",E)] L ∧ M (Lh + 8#64) = .word Nv ∧
    (∀ x, x.toNat < H.toNat → ¬ HdW Lh x → M x = M0 x) ∧ OnlyHeap Gk G ∧
    ∃ Pn Cn Hc : BitVec 64, M Lh = .word Pn ∧ M (Lh + 16#64) = .word Cn ∧ HeapIs G Hc ∧ H.toNat ≤ Hc.toNat ∧
      N.toNat < Cn.toNat ∧ Pn.toNat + E.toNat * Cn.toNat ≤ Hc.toNat ∧
      ((Pn = P ∧ Cn = Cp) ∨ (H.toNat ≤ Pn.toNat ∧ Cn.toNat = 2 * Cp.toNat))

/-- Postcondition of `lst_push`. -/
def LPPost (Lh E P N Cp H : BitVec 64) (M0 : Mem) (Gk : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) : Prop :=
  (∀ x, x.toNat < H.toNat → ¬ HdW Lh x → M' x = M0 x) ∧ OnlyHeap Gk G' ∧
    ∃ Pn Cn Hc : BitVec 64, v = .val (.word (Pn + N * E)) ∧ LHd Lh Pn (N + 1#64) Cn M' ∧ HeapIs G' Hc ∧
      H.toNat ≤ Hc.toNat ∧ N.toNat < Cn.toNat ∧ Pn.toNat + E.toNat * Cn.toNat ≤ Hc.toNat ∧
      ((Pn = P ∧ Cn = Cp) ∨ (H.toNat ≤ Pn.toNat ∧ Cn.toNat = 2 * Cp.toNat))

theorem hdw_toNat {Lh : BitVec 64} (hL : Lh.toNat + 24 ≤ 33806089496) :
    (Lh + 8#64).toNat = Lh.toNat + 8 ∧ (Lh + 16#64).toNat = Lh.toNat + 16 := by
  constructor <;> (simp [BitVec.toNat_add]; omega)

/-- The tail of `lst_push`: `st l + 8, n + 1; return lds(l + 0) + n * esz`. -/
theorem lstPush_tail (Lh E P N Cp H : BitVec 64) (M0 : Mem) (Gk : GA) (hL : Lh.toNat + 24 ≤ 33806089496)
    (hwh : ¬ HdW Lh w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (LPJ Lh E P N Cp H N M0 Gk) (fun _ _ _ => False)
      (LPPost Lh E P N Cp H M0 Gk)
      (.seq (.store (.op .add [.var .local (ofString "l"),.const 8#64])
          (.op .add [.var .local (ofString "n"),.const 1#64]))
        (.return (.op .add [.load .one (.op .add [.var .local (ofString "l"),.const 0#64]),
          .panop .mul [.var .local (ofString "n"),.var .local (ofString "esz")]]))) := by
  obtain ⟨e8,e16⟩ := hdw_toNat hL
  have n8 : Lh + 8#64 ≠ Lh := fun h => by rw [h] at e8; omega
  have n816 : Lh + 8#64 ≠ Lh + 16#64 := fun h => by rw [h] at e8; omega
  refine aqgd_seq (Q := LPJ Lh E P N Cp H (N + 1#64) M0 Gk) ?_ ?_
  · refine aqgd_storeD _ _ (fun s G _ _ hG pre _ => ?_)
      (fun s x _ _ _ _ pre _ ev => ⟨N + 1#64,by
        simp [EV,evalHOLExact,evalListHOLExact,pre.1 (ofString "n",N) (by simp),wordOpHOL,wordOp,valueIsWord,
          valueWord] at ev; exact ev.symm⟩)
    unfold GIs at hG; subst hG
    obtain ⟨lk,_,fr,oh,Pn,Cn,Hc,hP,hC,hH,rest⟩ := pre
    refine ⟨Lh + 8#64,ev_addc s _ Lh 8#64 (lk (ofString "l",Lh) (by simp)),fun h => hwh (Or.inr (Or.inl h)),
      fun y ev => ?_⟩
    simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "n",N) (by simp),wordOpHOL,wordOp,valueIsWord,
      valueWord] at ev
    subst ev
    refine ⟨lk,by simp,fun x hx hh => ?_,oh,Pn,Cn,Hc,by simp [Ne.symm n8]; exact hP,by simp [n816.symm]; exact hC,
      hH,rest⟩
    have : x ≠ Lh + 8#64 := fun h => hh (Or.inr (Or.inl h))
    simp only [this,if_false]; exact fr x hx hh
  · refine aqgd_return _ (fun s v G' _ hG pre _ ev => ?_)
    unfold GIs at hG; subst hG
    obtain ⟨lk,h8,fr,oh,Pn,Cn,Hc,hP,hC,hH,rest⟩ := pre
    simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "n",N) (by simp),lk (ofString "l",Lh) (by simp),
      lk (ofString "esz",E) (by simp),wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL,memLoadHOLExact,hP] at ev
    by_cases hm : s.memaddrs Lh
    · simp [hm] at ev
      subst ev
      exact ⟨fr,oh,Pn,Cn,Hc,rfl,⟨hP,h8,hC⟩,hH,rest⟩
    · simp [hm] at ev

#print axioms lstPush_tail

/-- `name = lds(l + off)` with the loaded word known. -/
theorem aqgd_lhdDec {Rm : Mem → GA → Prop} {pairs : List (MlS × BitVec 64)} {Lh : BitVec 64} (name : MlS)
    (off val : BitVec 64) {Qb Q : GA → Mem → GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop} {body : ProgHOL 64}
    (hname : ∀ p ∈ pairs, p.1 ≠ name)
    (ht : (ofString "l",Lh) ∈ pairs) (hval : ∀ M G, Rm M G → M (Lh + off) = .word val)
    (hb : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => LK ((name,val) :: pairs) L ∧ Rm M G) Qb RR body)
    (hq : ∀ L M (G : GA) L' M' G', LK pairs L ∧ Rm M G → Qb L' M' G' →
      Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (fun L M G => LK pairs L ∧ Rm M G) Q RR
      (.dec name .one (.load .one (.op .add [.var .local (ofString "l"),.const off])) body) :=
  aqgd_dec name .one _ (fun _ => rfl)
    (fun s v H _ _ ⟨hl,hm⟩ _ ev _ => by
      rw [ev_load_off s _ Lh off v (lk_get hl _ _ ht) ev,hval _ _ hm]
      exact ⟨lk_cons hl _ _ hname,hm⟩)
    hb hq

theorem mul_nat {a b : BitVec 64} (h : a.toNat * b.toNat < 2 ^ 64) : (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h

/-- Locals of `lst_push` after the two header loads. -/
def lpPs (Lh E N Cp : BitVec 64) : List (MlS × BitVec 64) :=
  [(ofString "cap",Cp),(ofString "n",N),(ofString "l",Lh),(ofString "esz",E)]

/-- State in the growth branch after `memcpy`. -/
def LPG2 (Lh E N Cp X : BitVec 64) (M0 : Mem) (Gk : GA) (L : GA) (M : Mem) (G : GA) : Prop :=
  LK ((ofString "np",X) :: lpPs Lh E N Cp) L ∧ (∀ x, x.toNat < X.toNat → M x = M0 x) ∧ OnlyHeap Gk G ∧
    ∃ Hc : BitVec 64, HeapIs G Hc ∧ X.toNat + E.toNat * Cp.toNat * 2 ≤ Hc.toNat

/-- `st l + 0, np; st l + 16, cap * 2` in the growth branch. -/
theorem lstPush_growStores (Lh E P N Cp H X : BitVec 64) (M0 : Mem) (Gk : GA) {RR : ValueHOL 64 → Mem → GA → Prop}
    (hL : Lh.toNat + 24 ≤ H.toNat) (hHE : H.toNat ≤ 33806089496) (hwh : ¬ HdW Lh w) (hd : LHd Lh P N Cp M0)
    (hNC : N = Cp) (hC0 : 0 < Cp.toNat) (hE1 : 1 ≤ E.toNat) (hsz : E.toNat * Cp.toNat * 2 ≤ 33806089496)
    (hHX : H.toNat ≤ X.toNat) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (LPG2 Lh E N Cp X M0 Gk)
      (fun L M G => LK ((ofString "np",X) :: lpPs Lh E N Cp) L ∧ LPJ Lh E P N Cp H N M0 Gk L M G) RR
      (.seq (.store (.op .add [.var .local (ofString "l"),.const 0#64]) (.var .local (ofString "np")))
        (.store (.op .add [.var .local (ofString "l"),.const 16#64])
          (.panop .mul [.var .local (ofString "cap"),.const 2#64]))) := by
  obtain ⟨e8,e16⟩ := hdw_toNat (Lh := Lh) (by omega)
  have n8 : Lh + 8#64 ≠ Lh := fun h => by rw [h] at e8; omega
  have n16 : Lh + 16#64 ≠ Lh := fun h => by rw [h] at e16; omega
  have n816 : Lh + 8#64 ≠ Lh + 16#64 := fun h => by rw [h] at e8; omega
  have hCE : Cp.toNat ≤ E.toNat * Cp.toNat := Nat.le_mul_of_pos_left _ hE1
  have ec : (Cp * 2#64).toNat = 2 * Cp.toNat := by
    rw [mul_nat (by simp; omega)]; simp; omega
  refine aqgd_seq (Q := fun L M G => LK ((ofString "np",X) :: lpPs Lh E N Cp) L ∧ M Lh = .word X ∧
      (∀ x, x.toNat < X.toNat → x ≠ Lh → M x = M0 x) ∧ OnlyHeap Gk G ∧
      ∃ Hc : BitVec 64, HeapIs G Hc ∧ X.toNat + E.toNat * Cp.toNat * 2 ≤ Hc.toNat) ?_ ?_
  · refine aqgd_storeD _ _ (fun s G _ _ hG pre _ => ?_)
      (fun s x _ _ _ _ pre _ ev => ⟨X,by
        simp [EV,evalHOLExact,pre.1 (ofString "np",X) (by simp)] at ev; exact ev.symm⟩)
    unfold GIs at hG; subst hG
    obtain ⟨lk,fr,oh,hh⟩ := pre
    have ea := ev_addc s _ Lh 0#64 (lk (ofString "l",Lh) (by simp [lpPs]))
    simp only [BitVec.add_zero] at ea
    refine ⟨Lh,ea,fun h => hwh (Or.inl h),fun y ev => ?_⟩
    simp [EV,evalHOLExact,lk (ofString "np",X) (by simp)] at ev
    subst ev
    refine ⟨lk,by simp,fun x hx hne => ?_,oh,hh⟩
    simp only [hne,if_false]; exact fr x hx
  · refine aqgd_storeD _ _ (fun s G _ _ hG pre _ => ?_)
      (fun s x _ _ _ _ pre _ ev => ⟨Cp * 2#64,by
        simp [EV,evalHOLExact,evalListHOLExact,pre.1 (ofString "cap",Cp) (by simp [lpPs]),panOpHOL,valueIsWord,
          valueWord] at ev; exact ev.symm⟩)
    unfold GIs at hG; subst hG
    obtain ⟨lk,hX,fr,oh,Hc,hHc,le⟩ := pre
    refine ⟨Lh + 16#64,ev_addc s _ Lh 16#64 (lk (ofString "l",Lh) (by simp [lpPs])),
      fun h => hwh (Or.inr (Or.inr h)),fun y ev => ?_⟩
    simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "cap",Cp) (by simp [lpPs]),panOpHOL,valueIsWord,
      valueWord] at ev
    subst ev
    refine ⟨lk,lk_tail lk,?_,fun x hx hh => ?_,oh,X,Cp * 2#64,Hc,?_,by simp,hHc,by omega,?_,?_,
      Or.inr ⟨hHX,ec⟩⟩
    · simp only [n816,if_false]
      rw [fr _ (by omega) n8]; exact hd.2.1
    · have h16 : x ≠ Lh + 16#64 := fun h => hh (Or.inr (Or.inr h))
      simp only [h16,if_false]
      exact fr x (by omega) (fun h => hh (Or.inl h))
    · simp only [n16.symm,if_false]; exact hX
    · rw [ec]; subst hNC; omega
    · rw [ec]
      have : E.toNat * (2 * Cp.toNat) = E.toNat * Cp.toNat * 2 := by ring
      omega

#print axioms lstPush_growStores

/-- State in the growth branch right after `alloc`. -/
def LPG1 (Lh E N Cp X : BitVec 64) (M0 : Mem) (Gk : GA) (L : GA) (M : Mem) (G : GA) : Prop :=
  LK ((ofString "np",X) :: lpPs Lh E N Cp) L ∧ M = M0 ∧ OnlyHeap Gk G ∧
    ∃ Hc : BitVec 64, HeapIs G Hc ∧ X.toNat + E.toNat * Cp.toNat * 2 ≤ Hc.toNat

/-- `memcpy(np, lds(l + 0), esz * n)` in the growth branch: only `[X, X + esz·n)` changes. -/
theorem lstPush_growMc (Lh E P N Cp H X : BitVec 64) (M0 : Mem) (Gk : GA) {RR : ValueHOL 64 → Mem → GA → Prop}
    (hw : w.toNat < H.toNat) (hd : LHd Lh P N Cp M0) (hNC : N = Cp) (hsz : E.toNat * Cp.toNat * 2 ≤ 33806089496)
    (hX8 : X.toNat % 8 = 0) (hHX : H.toNat ≤ X.toNat) (hXE : X.toNat + E.toNat * Cp.toNat * 2 ≤ 33806089496) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (LPG1 Lh E N Cp X M0 Gk) (LPG2 Lh E N Cp X M0 Gk) RR
      (.call (some (none,none)) (ofString "memcpy") [.var .local (ofString "np"),
        .load .one (.op .add [.var .local (ofString "l"),.const 0#64]),
        .panop .mul [.var .local (ofString "esz"),.var .local (ofString "n")]]) := by
  subst hNC
  have eEN : (E * N).toNat = E.toNat * N.toNat := mul_nat (by omega)
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ∃ S : BitVec 64, (L.lookup (ofString "dst") = some (.val (.word X)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧
        L.lookup (ofString "n") = some (.val (.word (E * N)))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ MWin X (E * N).toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' _
    exact aqgd_exE (fun S => memcpy_wn X S (E * N) (by omega)
      (mwin_belowS hX8 (by omega) (by omega)) M0' G0')
  · intro F s values callee rs _ H' hG ⟨lk,hM,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    simp [EV,evalHOLExact,lk (ofString "np",X) (by simp)] at ev1; subst ev1
    have e2 := ev_load_off s _ Lh 0#64 v2 (lk (ofString "l",Lh) (by simp [lpPs])) ev2
    simp only [BitVec.add_zero,hM,hd.1] at e2; subst e2
    simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "esz",E) (by simp [lpPs]),
      lk (ofString "n",N) (by simp [lpPs]),panOpHOL,valueIsWord,valueWord] at ev3; subst ev3
    have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
    exact ⟨P,⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
      by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lk,hM,oh,hh⟩ ⟨hG,fr⟩
    subst hG hM
    exact ⟨lk,fun x hx => fr x (mwin_belowS hX8 (by omega) hx),oh,hh⟩

#print axioms lstPush_growMc

/-- Entry state of `lst_push` after the two header loads. -/
def LPS2 (Lh E N Cp H : BitVec 64) (M0 : Mem) (Gk : GA) (L : GA) (M : Mem) (G : GA) : Prop :=
  LK (lpPs Lh E N Cp) L ∧ (M = M0 ∧ HeapIs G H ∧ G = Gk)

/-- The growth branch `np = alloc(esz * cap * 2); memcpy(...); st l + 0, np; st l + 16, cap * 2`. -/
theorem lstPush_grow (Lh E P N Cp H : BitVec 64) (M0 : Mem) (Gk : GA) {RR : ValueHOL 64 → Mem → GA → Prop}
    (hL : Lh.toNat + 24 ≤ H.toNat) (hHE : H.toNat ≤ 33806089496) (hw : w.toNat < H.toNat) (hwh : ¬ HdW Lh w)
    (hd : LHd Lh P N Cp M0) (hC0 : 0 < Cp.toNat) (hE1 : 1 ≤ E.toNat)
    (hsz : E.toNat * Cp.toNat * 2 ≤ 33806089496) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => LPS2 Lh E N Cp H M0 Gk L M G ∧ N = Cp) (LPJ Lh E P N Cp H N M0 Gk) RR
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul [.var .local (ofString "esz"),.var .local (ofString "cap")],.const 2#64]]
        (.seq (.call (some (none,none)) (ofString "memcpy") [.var .local (ofString "np"),
          .load .one (.op .add [.var .local (ofString "l"),.const 0#64]),
          .panop .mul [.var .local (ofString "esz"),.var .local (ofString "n")]])
          (.seq (.store (.op .add [.var .local (ofString "l"),.const 0#64]) (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"),.const 16#64])
              (.panop .mul [.var .local (ofString "cap"),.const 2#64]))))) := by
  have eS : (E * Cp * 2#64).toNat = E.toNat * Cp.toNat * 2 := by
    have hc : (E * Cp).toNat = E.toNat * Cp.toNat := mul_nat (by omega)
    rw [mul_nat (by rw [hc]; simp; omega),hc]; simp
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word (E * Cp * 2#64))) ∧ M = M0' ∧ HeapIs G (hpOf G0')) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word (hpOf G0')) ∧ M' = M0' ∧ (hpOf G0').toNat % 8 = 0 ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        (hpOf G0').toNat + (E * Cp * 2#64).toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L M G => ∃ X : BitVec 64, LPG1 Lh E N Cp X M0 Gk L M G ∧
      (X.toNat % 8 = 0 ∧ H.toNat ≤ X.toNat ∧ X.toNat + E.toNat * Cp.toNat * 2 ≤ 33806089496 ∧ N = Cp))
    (Qc := LPJ Lh E P N Cp H N M0 Gk) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocNA_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) (E * Cp * 2#64) (hpOf G0') M0' G0') ?_ (fun _ => rfl) ?_
    (aqgd_exE (fun X => aqgd_pureE (fun ⟨a,b,c,d⟩ => aqgd_seq (lstPush_growMc Lh E P N Cp H X M0 Gk hw hd d hsz a b
      (by omega)) (aqgd_conseq (lstPush_growStores Lh E P N Cp H X M0 Gk hL hHE hwh hd d hC0 hE1 hsz b)
        (fun _ _ _ h => h) (fun _ _ _ h => h.2) (fun _ _ _ h => h))))) ?_
  · intro F s values callee rs _ H' hG ⟨⟨lk,_,hH,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "esz",E) (by simp [lpPs]),
      lk (ofString "cap",Cp) (by simp [lpPs]),panOpHOL,valueIsWord,valueWord] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,by rw [hpOf_eq hH]; exact hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨lk,hM,hH,hG⟩,hNC⟩ ⟨⟨ev,eM,al,H',hH',c1,c2⟩,oh'⟩ _
    subst ev eM hM hG
    rw [hpOf_eq hH] at al c1 ⊢
    rw [eS] at c1
    exact ⟨H,⟨lk_update' lk _ _ (by simp (config := {decide := true}) [lpPs]),rfl,oh',H',hH',c1⟩,al,le_refl _,
      by omega,hNC⟩
  · intro L M G L' M' G' _ ⟨lk,rest⟩
    exact ⟨lk_res lk _ _ (by simp (config := {decide := true})),rest⟩

#print axioms lstPush_grow

/-- The actual `lst_push(l, esz)` on a valid list header. -/
theorem lstPush_spec (Lh E P N Cp H : BitVec 64) (M0 : Mem) (Gk : GA)
    (hL : Lh.toNat + 24 ≤ H.toNat) (hHE : H.toNat ≤ 33806089496) (hw : w.toNat < H.toNat) (hwh : ¬ HdW Lh w)
    (hd : LHd Lh P N Cp M0) (hNC : N.toNat ≤ Cp.toNat) (hC0 : 0 < Cp.toNat) (hE1 : 1 ≤ E.toNat)
    (hbuf : P.toNat + E.toNat * Cp.toNat ≤ H.toNat) (hsz : E.toNat * Cp.toNat * 2 ≤ 33806089496) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => (LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0 ∧ HeapIs G H) ∧ G = Gk)
      (fun _ _ _ => False) (LPPost Lh E P N Cp H M0 Gk) (sourceFunctionBody Guest.guestFn_lst_push) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_lst_push,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aqgd_conseq (P := fun L M G => LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ (M = M0 ∧ HeapIs G H ∧ G = Gk))
    ?_ (fun L M G ⟨⟨lk,hM,hH⟩,hG⟩ => ⟨lk,hM,hH,hG⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_lhdDec (Lh := Lh) (Qb := fun _ _ _ => False) (ofString "n") 8#64 N (by simp (config := {decide := true}))
    (by simp) (fun M _ ⟨hM,_⟩ => by rw [hM]; exact hd.2.1) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_lhdDec (Lh := Lh) (Qb := fun _ _ _ => False) (ofString "cap") 16#64 Cp (by simp (config := {decide := true}))
    (by simp) (fun M _ ⟨hM,_⟩ => by rw [hM]; exact hd.2.2) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_seq (Q := LPJ Lh E P N Cp H N M0 Gk) ?_
    (aqgd_conseq (lstPush_tail Lh E P N Cp H M0 Gk (by omega) hwh) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ h => h))
  refine aqgd_iteD (CT := fun _ _ _ => N = Cp) (CF := fun _ _ _ => N.toNat < Cp.toNat) _ ?_
    (aqgd_conseq (lstPush_grow Lh E P N Cp H M0 Gk hL hHE hw hwh hd hC0 hE1 hsz) (fun _ _ _ h => h)
      (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h) ?_ (fun _ _ _ h => h))
  · intro F s x G _ _ _ ⟨hl,_⟩ _ ev
    simp [EV,evalHOLExact,hl (ofString "n",N) (by simp),hl (ofString "cap",Cp) (by simp)] at ev
    simp only [Compiler.Encoders.Asm.wordCmpHOL] at ev
    by_cases e : Cp.toNat ≤ N.toNat
    · have : N = Cp := BitVec.eq_of_toNat_eq (by omega)
      subst this
      exact ⟨fun _ => rfl,fun h => by simp at ev; subst ev; exact absurd h (by decide)⟩
    · refine ⟨fun h => absurd ?_ h,fun _ => by omega⟩
      have : N < Cp := BitVec.lt_def.mpr (by omega)
      simp [this] at ev; exact ev.symm
  · intro L M G ⟨⟨lk,hM,hH,hG⟩,lt⟩
    subst hM hG
    exact ⟨lk,hd.2.1,fun _ _ _ => rfl,fun _ _ => rfl,P,Cp,H,hd.1,hd.2.2,hH,le_refl _,lt,hbuf,Or.inl ⟨rfl,rfl⟩⟩

#print axioms lstPush_spec

end lp
end InitECandidate.Runtime
