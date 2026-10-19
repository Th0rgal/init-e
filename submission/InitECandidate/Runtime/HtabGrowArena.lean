import InitECandidate.Runtime.HtabInsertArena
import InitECandidate.Runtime.OriginalHashInsertCode
import InitECandidate.Runtime.OriginalAllocationCode
import InitECandidate.Runtime.OriginalMemzeroCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → Prop}

theorem aqm_ex {α : Type} {P : α → HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop}
    {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {p : ProgHOL 64}
    (h : ∀ a, AQM SP0 P0 FM G0 w Vn (P a) Q RR p) : AQM SP0 P0 FM G0 w Vn (fun L M => ∃ a, P a L M) Q RR p :=
  fun F s code dom aw sl ⟨a,pre⟩ => h a F s code dom aw sl pre

/-- Header cells written so far, by offset. -/
def Cells (M : Mem) (T : BitVec 64) (cs : List (BitVec 64 × BitVec 64)) : Prop :=
  ∀ p ∈ cs, M (T + p.1) = .word p.2

theorem cells_store {M : Mem} {T : BitVec 64} {cs : List (BitVec 64 × BitVec 64)} (h : Cells M T cs)
    (off y : BitVec 64) (hoff : ∀ p ∈ cs, p.1 ≠ off) :
    Cells (fun x => if x = T + off then .word y else M x) T ((off,y) :: cs) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp
  · have ne : T + p.1 ≠ T + off := fun e => hoff p hp (add_left_cancel e)
    simp only [if_neg ne]
    exact h p hp

theorem cells_hdr {M : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64}
    (h : Cells M T [(24#64,N),(64#64,OPS),(56#64,OS),(48#64,US),(40#64,VS),(32#64,KS),(16#64,C),(8#64,SD),(0#64,KL)]) :
    Hdr M T KL SD C N KS VS US OS OPS :=
  ⟨h (0#64,KL) (by simp),h (8#64,SD) (by simp),h (16#64,C) (by simp),h (24#64,N) (by simp),h (32#64,KS) (by simp),
    h (40#64,VS) (by simp),h (48#64,US) (by simp),h (56#64,OS) (by simp),h (64#64,OPS) (by simp)⟩

/-- `insert_raw` spec with unspecified key and value arguments. -/
theorem insertRaw_aqm_ex (T : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True) (fun _ M' => MI P0 T E M0 KL SD C (N + 1#64) KS VS US OS OPS M')
      (sourceFunctionBody Guest.guestFn_htab_insert_raw) := by
  intro F s code dom aw sl ⟨⟨Kk,V,hl⟩,hh,hm⟩
  exact insertRaw_aqm T Kk V E KL SD C N KS VS US OS OPS b lay M0 hw F s code dom aw sl ⟨hl,hh,hm⟩

theorem aqm_ex' {α : Type} {Fa : α → Prop} {P : α → HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop}
    {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {p : ProgHOL 64}
    (h : ∀ a, Fa a → AQM SP0 P0 FM G0 w Vn (P a) Q RR p) :
    AQM SP0 P0 FM G0 w Vn (fun L M => ∃ a, Fa a ∧ P a L M) Q RR p :=
  fun F s code dom aw sl ⟨a,fa,pre⟩ => h a fa F s code dom aw sl pre

/-- A fresh 8-aligned block of `len` bytes at or above `P0`, below `HEAP_END`. -/
def Fresh (P0 A : BitVec 64) (len : Nat) : Prop :=
  P0.toNat ≤ A.toNat ∧ A.toNat + len ≤ 33806089496 ∧ A.toNat % 8 = 0

/-- `name = alloc(size)` with a constant size: the continuation knows a fresh block. -/
theorem aqm_allocDec {R : Mem → Prop} {pairs : List (MlS × BitVec 64)} (name : MlS) (arg : ExpHOL 64)
    (size : BitVec 64) {cont : ProgHOL 64} {RR : ValueHOL 64 → Mem → Prop}
    (hname : ∀ p ∈ pairs, p.1 ≠ name)
    (harg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LK pairs s.locals → EV s arg = some x →
      x = .val (.word size))
    (hc : ∀ A, Fresh P0 A size.toNat →
      AQM SP0 P0 FM G0 w (fun _ => True) (fun L M => LK ((name,A) :: pairs) L ∧ R M) (fun _ _ => True) RR cont) :
    AQM SP0 P0 FM G0 w (fun _ => True) (fun L M => LK pairs L ∧ R M) (fun _ _ => True) RR
      (.decCall name .one (ofString "alloc") [arg] cont) := by
  refine aqm_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' L M => L.lookup (ofString "n") = some (.val (.word size)) ∧ M = M0')
    (RRe := fun _ M0' v M' => M' = M0' ∧ ∃ hp : BitVec 64, v = .val (.word hp) ∧ P0.toNat ≤ hp.toNat ∧
        hp.toNat + size.toNat ≤ 33806089496 ∧ hp.toNat % 8 = 0)
    (Pc := fun L M => ∃ A, Fresh P0 A size.toNat ∧ LK ((name,A) :: pairs) L ∧ R M) (Qc := fun _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) (fun _ M0' _ => alloc_aqm size M0') ?_
    (fun _ => rfl) ?_ (aqm_ex' (fun A fa => hc A fa)) (fun _ _ _ _ _ _ => trivial)
  · intro F s values callee rs _ ⟨hl,_⟩ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    rw [harg s x hl ex] at lookup
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩
  · intro L M v M' ⟨hl,hr⟩ ⟨eM,hp,ev,lo,hi,al⟩ _
    subst eM ev
    exact ⟨hp,⟨lo,hi,al⟩,lk_cons hl _ _ hname,hr⟩

theorem mwin_ge {D x : BitVec 64} {N : Nat} (hx : MWin D N x) (al : D.toNat % 8 = 0) (fit : D.toNat + N < 2 ^ 64) :
    D.toNat ≤ x.toNat ∧ x.toNat < D.toNat + N := by
  obtain ⟨j,hj,h | h⟩ := hx
  · have : (D + BitVec.ofNat 64 j).toNat = D.toNat + j := by rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    subst h; omega
  · have e1 : (D + BitVec.ofNat 64 j).toNat = D.toNat + j := by rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    have e2 := panByteAlign_toNat64 (D + BitVec.ofNat 64 j)
    rw [e1,← h] at e2
    have := Nat.div_add_mod D.toNat 8
    have := Nat.div_le_div_right (c := 8) (Nat.le_add_right D.toNat j)
    have := Nat.div_mul_le_self (D.toNat + j) 8
    omega

/-- Header cells being rewritten: the listed cells, the current locals, and agreement with the entry memory
outside the footprint. -/
def HW (P0 T : BitVec 64) (E : BitVec 64 → Prop) (M0 : Mem) (pairs : List (MlS × BitVec 64)) (cs : List (BitVec 64 × BitVec 64))
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : Mem) : Prop :=
  LK pairs L ∧ Cells M T cs ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x

/-- A header store `st t + off, v` with a known word value. -/
theorem aqm_cellStore {P0 T : BitVec 64} {E : BitVec 64 → Prop} {M0 : Mem} {pairs : List (MlS × BitVec 64)}
    {cs : List (BitVec 64 × BitVec 64)} (off val : BitVec 64) (v : ExpHOL 64)
    (ht : (ofString "t",T) ∈ pairs) (small : off.toNat < 72)
    (hdr : ∀ x : BitVec 64, T.toNat ≤ x.toNat → x.toNat < T.toNat + 72 → E x) (eE : T.toNat + 72 < 2 ^ 64)
    (hw : ¬ Foot P0 T E w) (hoff : ∀ p ∈ cs, p.1 ≠ off)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LK pairs s.locals → EV s v = some x →
      x = .val (.word val)) :
    AQM SP0 P0 FM G0 w (fun _ => True) (HW P0 T E M0 pairs cs) (HW P0 T E M0 pairs ((off,val) :: cs)) RR
      (.store (.op .add [.var .local (ofString "t"),.const off]) v) := by
  have fa : Foot P0 T E (T + off) := by
    apply hdr <;> rw [BitVec.toNat_add_of_lt (by omega)] <;> omega
  refine aqm_store' _ _ ?_ ?_
  · intro F s a _ ⟨hl,hc,ag⟩ _ ev
    have htl := lk_get hl _ _ ht
    simp [EV,evalHOLExact,evalListHOLExact,htl,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨fun e => hw (e ▸ fa),fun y ey => ?_⟩
    have hy : y = val := by
      have := hv s _ hl ey
      simp only [ValueHOL.val.injEq,HolWordLab.word.injEq] at this
      exact this
    subst hy
    refine ⟨hl,cells_store hc off y hoff,fun x hx => ?_⟩
    have : x ≠ T + off := fun e => hx (e ▸ fa)
    simp only [if_neg this]
    exact ag x hx
  · intro F s x _ ⟨hl,_⟩ _ ev
    exact ⟨val,hv s x hl ev⟩

/-- The doubled layout after a grow: fresh arrays sized for twice the capacity. -/
theorem grow_newLay {P0 T : BitVec 64} {E : BitVec 64 → Prop} {KL SD C N KS VS US OS OPS NKS NVS NUS NOS NOPS K : BitVec 64} {b : Nat}
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b)
    (fk : Fresh P0 NKS (C * 2#64 * SD).toNat) (fv : Fresh P0 NVS (C * 2#64 * 8#64).toNat)
    (fu : Fresh P0 NUS (C * 2#64).toNat) (fo : Fresh P0 NOS (C * 2#64 * 8#64).toNat)
    (fp : Fresh P0 NOPS (C * 2#64 * 8#64).toNat) (hK : K.toNat ≤ N.toNat) :
    HLay P0 T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) := by
  have cHE : C.toNat ≤ 33806089496 := by have := arr_end lay.usedR lay.eEnd; omega
  have csd : C.toNat * SD.toNat ≤ 33806089496 := by have := arr_end lay.keysR lay.eEnd; omega
  have c2 : (C * 2#64).toNat = C.toNat * 2 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  have c2sd : (C * 2#64 * SD).toNat = C.toNat * 2 * SD.toNat := by
    rw [BitVec.toNat_mul,c2]; exact Nat.mod_eq_of_lt (by
      have : C.toNat * 2 * SD.toNat = 2 * (C.toNat * SD.toNat) := by ring
      omega)
  have c28 : (C * 2#64 * 8#64).toNat = C.toNat * 2 * 8 := by
    rw [BitVec.toNat_mul,c2]; exact Nat.mod_eq_of_lt (by simp; omega)
  obtain ⟨k1,k2,k3⟩ := fk; obtain ⟨v1,v2,_⟩ := fv; obtain ⟨u1,u2,u3⟩ := fu; obtain ⟨o1,o2,_⟩ := fo
  obtain ⟨p1,p2,_⟩ := fp
  rw [c2sd] at k2; rw [c28] at v2 o2 p2; rw [c2] at u2
  have cnt := lay.cnt
  exact { pow := by rw [c2,lay.pow]; ring
          fits := lay.fits
          sdAl := lay.sdAl
          ksAl := k3
          usAl := u3
          cnt := by rw [c2]; omega
          hdr := lay.hdr
          hdrP := lay.hdrP
          eEnd := lay.eEnd
          fresh := lay.fresh
          keysR := ⟨by have := lay.hdrP; omega,by rw [c2]; omega,fun x lo _ => lay.fresh x (by omega)⟩
          valsR := ⟨by have := lay.hdrP; omega,by rw [c2]; omega,fun x lo _ => lay.fresh x (by omega)⟩
          usedR := ⟨by have := lay.hdrP; omega,by rw [c2]; omega,fun x lo _ => lay.fresh x (by omega)⟩
          orderR := ⟨by have := lay.hdrP; omega,by rw [c2]; omega,fun x lo _ => lay.fresh x (by omega)⟩
          oposR := ⟨by have := lay.hdrP; omega,by rw [c2]; omega,fun x lo _ => lay.fresh x (by omega)⟩ }

/-- `htab_grow` locals after the header loads and `ncap`. -/
def grP (T C SD KS VS OS N : BitVec 64) : List (MlS × BitVec 64) :=
  [(ofString "ncap",C * 2#64),(ofString "nitems",N),(ofString "order",OS),(ofString "vals",VS),(ofString "keys",KS),
    (ofString "stride",SD),(ofString "cap",C),(ofString "t",T)]

set_option maxHeartbeats 4000000 in
/-- `htab_grow` under the real table layout: every word outside the footprint is kept in every outcome; a return
leaves a new layout (doubled capacity, fresh arrays, count at most the old count) whose header is in memory, with
memory agreeing with the entry outside the footprint. -/
theorem grow_aqm (T : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => LK [(ofString "t",T)] L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True)
      (fun _ M' => ∃ K NKS NVS NUS NOS NOPS : BitVec 64, K.toNat ≤ N.toNat ∧
        HLay P0 T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) ∧
        MI P0 T E M0 KL SD (C * 2#64) K NKS NVS NUS NOS NOPS M')
      (sourceFunctionBody Guest.guestFn_htab_grow) := by
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := lay.eEnd; omega
  have cHE : C.toNat ≤ 33806089496 := by have := arr_end lay.usedR lay.eEnd; omega
  have c2 : (C * 2#64).toNat = C.toNat * 2 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  have csd : C.toNat * SD.toNat ≤ 33806089496 := by have := arr_end lay.keysR lay.eEnd; omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_htab_grow,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aqm_conseq (P := fun L M => LK [(ofString "t",T)] L ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) ?_
    (fun L M h => ⟨h.1,h.2.1,fun x _ => by rw [h.2.2]⟩) (fun _ _ h => h) (fun _ _ h => h)
  refine aqm_hdrDec (ofString "cap") 16#64 C (by lkne) (by simp) (fun M h => h.1.2.2.1) ?_
  refine aqm_hdrDec (ofString "stride") 8#64 SD (by lkne) (by simp) (fun M h => h.1.2.1) ?_
  refine aqm_hdrDec (ofString "keys") 32#64 KS (by lkne) (by simp) (fun M h => h.1.2.2.2.2.1) ?_
  refine aqm_hdrDec (ofString "vals") 40#64 VS (by lkne) (by simp) (fun M h => h.1.2.2.2.2.2.1) ?_
  refine aqm_hdrDec (ofString "order") 56#64 OS (by lkne) (by simp) (fun M h => h.1.2.2.2.2.2.2.2.1) ?_
  refine aqm_hdrDec (ofString "nitems") 24#64 N (by lkne) (by simp) (fun M h => h.1.2.2.2.1) ?_
  refine aqm_dec (Pb := fun L M => LK (grP T C SD KS VS OS N) L ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
    (Qb := fun _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro F s v _ ⟨hl,hm⟩ _ ev _
    have hc := lk_get hl (ofString "cap") C (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,hc,panOpHOL,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨lk_cons hl _ _ (by lkne),hm⟩
  refine aqm_allocDec (ofString "nkeys") _ (C * 2#64 * SD) (by unfold grP; lkne) ?_ (fun NKS fk => ?_)
  · intro F s x hl ev
    have h1 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    have h2 := lk_get hl (ofString "stride") SD (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h1,h2,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  refine aqm_allocDec (ofString "nvals") _ (C * 2#64 * 8#64) (by unfold grP; lkne) ?_ (fun NVS fnvals => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h0,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  refine aqm_allocDec (ofString "nused") _ (C * 2#64) (by unfold grP; lkne) ?_ (fun NUS fnused => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,h0] at ev
    exact ev.symm
  refine aqm_allocDec (ofString "norder") _ (C * 2#64 * 8#64) (by unfold grP; lkne) ?_ (fun NOS fnorder => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h0,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  refine aqm_allocDec (ofString "norder_pos") _ (C * 2#64 * 8#64) (by unfold grP; lkne) ?_ (fun NOPS fnorder_pos => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h0,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  have hwP : w.toNat < P0.toNat := by by_contra h; exact hw (lay.fresh w (by omega))
  have nC := lay.cnt
  refine aqm_seq (Q := HW P0 T E M0 ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N) [(8#64,SD),(0#64,KL)]) (aqm_callSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' L M => L.lookup (ofString "dst") = some (.val (.word NUS)) ∧
      L.lookup (ofString "n") = some (.val (.word (C * 2#64))) ∧ M = M0')
    (RRe := fun _ M0' _ M' => ∀ x, ¬ MWin NUS (C * 2#64).toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ M0' _ => memzero_aqm NUS (C * 2#64) (by omega) (mwin_above (by have := fnused.1; omega) fnused.2.2
      (by have := fnused.2.1; omega)) M0') ?_ ?_) ?_
  · intro F s values callee rs _ ⟨hl,_⟩ _ args lookup
    have h1 := lk_get hl (ofString "nused") NUS (by simp)
    have h2 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,h1,h2] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_memzero_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩
  · intro L M v M' ⟨hl,hm⟩ h
    have hm' := mi_frame hm fitT (MWin NUS (C * 2#64).toNat) (fun x hx => by
      obtain ⟨lo,_⟩ := mwin_ge hx fnused.2.2 (by have := fnused.2.1; omega)
      have := fnused.1; have := lay.hdrP
      exact ⟨lay.fresh x (by omega),by omega⟩) h
    refine ⟨hl,fun p hp => ?_,hm'.2⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl
    · exact hm'.1.2.1
    · exact hm'.1.1
  refine aqm_seq (aqm_cellStore 16#64 (C * 2#64) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 32#64 (NKS) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "nkeys") (NKS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 40#64 (NVS) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "nvals") (NVS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 48#64 (NUS) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "nused") (NUS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 56#64 (NOS) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "norder") (NOS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 64#64 (NOPS) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "norder_pos") (NOPS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 24#64 (0#64) _ (by simp [grP]) (by decide) lay.hdr fitT hw
    (by simp) (fun s x hl ev => by simp [EV,evalHOLExact] at ev; exact ev.symm)) ?_
  refine aqm_dec (Pb := fun L M => ∃ K : BitVec 64, LK ((ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat ≤ N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) (Qb := fun _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro F s v _ ⟨hl,hc,ag⟩ _ ev _
    simp [EV,evalHOLExact] at ev
    subst ev
    exact ⟨0#64,lk_cons hl _ _ (by unfold grP; lkne),by simp,cells_hdr hc,ag⟩
  have newLay : ∀ K : BitVec 64, K.toNat ≤ N.toNat → HLay P0 T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) :=
    fun K hK => grow_newLay lay fk fnvals fnused fnorder fnorder_pos hK
  refine aqm_seq (Q := fun L M => ∃ K : BitVec 64, LK ((ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat ≤ N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x)
    (aqm_while (C := fun L M => ∃ K : BitVec 64, L.lookup (ofString "k") = some (.val (.word K)) ∧ K.toNat < N.toNat)
      _ ?_ ?_) (aqm_return _ ?_)
  · intro F s x _ ⟨K,hl,hK,_⟩ _ ev nz
    have h1 := lk_get hl (ofString "k") K (by simp)
    have h2 := lk_get hl (ofString "nitems") N (by simp [grP])
    simp [EV,evalHOLExact,h1,h2] at ev
    have small : K.toNat < 2 ^ 63 ∧ N.toNat < 2 ^ 63 := by constructor <;> omega
    rw [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,holAsmSignedLess_small K N small.1 small.2] at ev
    refine ⟨K,h1,?_⟩
    by_contra hge
    simp [hge] at ev
    exact nz ev.symm
  · refine aqm_dec (Pb := fun L M => ∃ I K : BitVec 64, LK ((ofString "i",I) :: (ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat < N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) (Qb := fun L M => ∃ K : BitVec 64, LK ((ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat ≤ N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) _ _ _ (fun _ => rfl) ?_ ?_ ?_
    · intro F s v _ ⟨⟨K,hl,_,hh,ag⟩,K',hk',hlt⟩ _ ev _
      have h1 := lk_get hl (ofString "k") K (by simp)
      rw [h1] at hk'; cases hk'
      obtain ⟨y,rfl⟩ := ev_load_one_word s _ v ev
      exact ⟨y,K,lk_cons hl _ _ (by unfold grP; lkne),hlt,hh,ag⟩
    · refine aqm_seq (Q := fun L M => ∃ I K : BitVec 64, LK ((ofString "i",I) :: (ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat < N.toNat ∧
      Hdr M T KL SD (C * 2#64) (K + 1#64) NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) (aqm_callSpec (Vn' := fun _ => True)
        (Pe := fun _ M0' L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ M = M0')
        (RRe := fun _ M0' _ M' => ∀ K : BitVec 64, M0' (T + 24#64) = .word K →
          MI P0 T E M0' KL SD (C * 2#64) (K + 1#64) NKS NVS NUS NOS NOPS M')
        _ _ _ _ _ originalRuntimeCode_hashInsert_lookup (by simp) ?_ ?_ ?_) (aqm_assignLocal _ _ ?_)
      · intro L0 M0' ⟨I,K,hl,hK,hh,ag⟩
        refine aqm_conseq (insertRaw_aqm_ex T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1)
          (newLay K (by omega)) M0' hw) (fun L M ⟨h1,h2⟩ => ⟨h1,h2 ▸ hh,h2⟩) (fun _ _ h => h) ?_
        intro v M' h K' hK'
        rw [hh.2.2.2.1] at hK'
        simp only [HolWordLab.word.injEq] at hK'
        subst hK'
        exact h
      · intro F s values callee rs _ ⟨I,K,hl,_,_⟩ _ args lookup
        have ht := lk_get hl (ofString "t") T (by simp [grP])
        have hks := lk_get hl (ofString "keys") KS (by simp [grP])
        have hi := lk_get hl (ofString "i") I (by simp)
        have hsd := lk_get hl (ofString "stride") SD (by simp [grP])
        have hvs := lk_get hl (ofString "vals") VS (by simp [grP])
        rw [evalListHOLFinite_eq_toExact] at args
        cases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "vals"),.panop .mul [.var .local (ofString "i"),.const 8#64]])) with
        | none => simp [evalListHOLExact,hx] at args
        | some x =>
          obtain ⟨y,rfl⟩ := ev_load_one_word s _ x hx
          simp only [evalListHOLExact] at args
          rw [hx] at args
          simp [evalListHOLExact,evalHOLExact,ht,hks,hi,hsd,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord] at args
          subst args
          rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
            originalRuntimeCode_hashInsert_lookup] at lookup
          simp only [Option.some.injEq,Prod.mk.injEq] at lookup
          obtain ⟨_,rfl,_⟩ := lookup
          refine ⟨⟨KS + I * SD,y,fun p hp => ?_⟩,rfl⟩
          simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
          rcases hp with rfl | rfl | rfl <;>
            simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
      · intro L M v M' ⟨I,K,hl,hK,hh,ag⟩ h
        have := h K hh.2.2.2.1
        exact ⟨I,K,hl,hK,this.1,fun x hx => (this.2 x hx).trans (ag x hx)⟩
      · intro F s v _ ⟨I,K,hl,hK,hh,ag⟩ _ ev
        have h1 := lk_get hl (ofString "k") K (by simp)
        simp [EV,evalHOLExact,evalListHOLExact,h1,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
        subst ev
        refine ⟨K + 1#64,lk_cons (fun p hp => hl p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))) _ _
          (by unfold grP; lkne),?_,hh,ag⟩
        rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
    · intro L M L' M' _ h
      obtain ⟨K,hl,hK,hh,ag⟩ := h
      exact ⟨K,lk_res hl _ _ (by unfold grP; lkne),hK,hh,ag⟩
  · intro F s v _ ⟨K,_,hK,hh,ag⟩ _ _
    exact ⟨K,NKS,NVS,NUS,NOS,NOPS,hK,newLay K hK,hh,ag⟩

#print axioms aqm_allocDec
#print axioms aqm_cellStore
#print axioms grow_newLay
#print axioms grow_aqm
end InitECandidate.Runtime
