import InitECandidate.Runtime.HtabGrowTail
/-!
Heap-aware `htab_grow`: the five allocations are tracked against the actual heap pointer, so the grown table's
arrays are known to lie in `[H0, H5)` between the entry heap pointer and a point at or below the exit heap pointer,
and the grown table is valid against the precise footprint `GrowFoot T H0` (its header plus the heap from `H0`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

/-- Footprint of a table grown from heap pointer `H0`: its header and the heap from `H0` on. -/
def GrowFoot (T H0 : BitVec 64) (x : BitVec 64) : Prop :=
  (T.toNat ≤ x.toNat ∧ x.toNat < T.toNat + 72) ∨ H0.toNat ≤ x.toNat

/-- `x` is a byte of one of the five table arrays. -/
def ArrOf (C SD KS VS US OS OPS : BitVec 64) (x : BitVec 64) : Prop :=
  (KS.toNat ≤ x.toNat ∧ x.toNat < KS.toNat + C.toNat * SD.toNat) ∨
    (VS.toNat ≤ x.toNat ∧ x.toNat < VS.toNat + C.toNat * 8) ∨
    (US.toNat ≤ x.toNat ∧ x.toNat < US.toNat + C.toNat) ∨
    (OS.toNat ≤ x.toNat ∧ x.toNat < OS.toNat + C.toNat * 8) ∨
    (OPS.toNat ≤ x.toNat ∧ x.toNat < OPS.toNat + C.toNat * 8)

/-- Every byte of the five table arrays satisfies `R`. -/
def LayIn (R : BitVec 64 → Prop) (C SD KS VS US OS OPS : BitVec 64) : Prop :=
  ∀ x : BitVec 64, ArrOf C SD KS VS US OS OPS x → R x

/-- An `AQM` proof at arena bound `H5` gives one at any bound `H`, under the premise `H = H5`. -/
theorem aqm_bound_eq {Vn : MlS → Prop} {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop}
    {RR : ValueHOL 64 → Mem → Prop} {p : ProgHOL 64} {H H5 : BitVec 64}
    (h : AQM SP0 H5 FM G0 w Vn P Q RR p) :
    AQM SP0 H FM G0 w Vn (fun L M => H = H5 ∧ P L M) (fun L M => H = H5 ∧ Q L M) (fun v M => H = H5 ∧ RR v M) p := by
  intro F s code dom aw sl ⟨e,pre⟩
  subst e
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl pre
  exact ⟨m,a,fun e => ⟨(n e).1,rfl,(n e).2⟩,fun v e => ⟨rfl,r v e⟩,c,b⟩

theorem aqmh_hdrDec {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} {R : Mem → Prop} {pairs : List (MlS × BitVec 64)}
    {T Hc : BitVec 64} (name : MlS) (off val : BitVec 64)
    {body : ProgHOL 64} (hname : ∀ p ∈ pairs, p.1 ≠ name) (ht : (ofString "t",T) ∈ pairs)
    (hval : ∀ M, R M → M (T + off) = .word val)
    (hb : AQMH SP0 P0 FM G0 w (fun _ => True) (fun L M H => LK ((name,val) :: pairs) L ∧ R M ∧ H = Hc)
      (fun _ _ _ => True) RR body) :
    AQMH SP0 P0 FM G0 w (fun _ => True) (fun L M H => LK pairs L ∧ R M ∧ H = Hc) (fun _ _ _ => True) RR
      (.dec name .one (.load .one (.op .add [.var .local (ofString "t"),.const off])) body) :=
  aqmh_dec name .one _ (fun _ => rfl)
    (fun s v H _ ⟨hl,hm,hh⟩ _ ev _ => by
      rw [ev_load_off s _ T off v (lk_get hl _ _ ht) ev,hval _ hm]
      exact ⟨lk_cons hl _ _ hname,hm,hh⟩)
    hb (fun _ _ _ _ _ _ _ _ => trivial)

/-- `name = alloc(size)` from heap pointer `Hc`: the continuation runs with `name = Hc` and heap pointer
`allocationEnd Hc size`, knowing the block fits, is aligned and sits at or above `P0`. -/
theorem aqmh_allocDec {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} {R : Mem → Prop} {pairs : List (MlS × BitVec 64)}
    (name : MlS) (arg : ExpHOL 64) (size Hc : BitVec 64) {cont : ProgHOL 64}
    (hname : ∀ p ∈ pairs, p.1 ≠ name)
    (harg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LK pairs s.locals → EV s arg = some x →
      x = .val (.word size))
    (hc : P0.toNat ≤ Hc.toNat → Hc.toNat + size.toNat ≤ (allocationEnd Hc size).toNat →
      (allocationEnd Hc size).toNat ≤ 33806089496 → (allocationEnd Hc size).toNat % 8 = 0 → Hc.toNat % 8 = 0 →
      AQMH SP0 P0 FM G0 w (fun _ => True) (fun L M H => LK ((name,Hc) :: pairs) L ∧ R M ∧ H = allocationEnd Hc size)
        (fun _ _ _ => True) RR cont) :
    AQMH SP0 P0 FM G0 w (fun _ => True) (fun L M H => LK pairs L ∧ R M ∧ H = Hc) (fun _ _ _ => True) RR
      (.decCall name .one (ofString "alloc") [arg] cont) := by
  refine aqmh_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' H0 L M H => L.lookup (ofString "n") = some (.val (.word size)) ∧ M = M0' ∧ H = H0)
    (RRe := fun _ M0' H0 v M' H' => M' = M0' ∧ v = .val (.word H0) ∧ H' = allocationEnd H0 size ∧
      P0.toNat ≤ H0.toNat ∧ H0.toNat + size.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0 ∧
      H0.toNat % 8 = 0)
    (Pc := fun L M H => (P0.toNat ≤ Hc.toNat ∧ Hc.toNat + size.toNat ≤ (allocationEnd Hc size).toNat ∧
      (allocationEnd Hc size).toNat ≤ 33806089496 ∧ (allocationEnd Hc size).toNat % 8 = 0 ∧ Hc.toNat % 8 = 0) ∧
      LK ((name,Hc) :: pairs) L ∧ R M ∧ H = allocationEnd Hc size) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) (fun _ M0' H0 _ => alloc_aqmh size H0 M0') ?_
    (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s values callee rs _ H _ ⟨hl,_⟩ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    rw [harg s x hl ex] at lookup
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M H v M' H' ⟨hl,hr,hh⟩ ⟨eM,ev,eH,lo,c1,fin,c3,al⟩ _
    subst hh eM ev eH
    exact ⟨⟨lo,c1,fin,c3,al⟩,lk_cons hl _ _ hname,hr,rfl⟩
  · intro F s code dom aw sl H hH ⟨⟨f1,f2,f3,f4,f5⟩,pre⟩
    exact hc f1 f2 f3 f4 f5 F s code dom aw sl H hH pre

/-- The grown layout at heap pointer `H5`, from the five allocation results chained from `H0`. -/
theorem grow_heapLay {T : BitVec 64} {E : BitVec 64 → Prop} {KL SD C N KS VS US OS OPS H0 H1 H2 H3 H4 H5 K : BitVec 64}
    {b : Nat} (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (p0 : P0.toNat ≤ H0.toNat)
    (a1 : H0.toNat + (C * 2#64 * SD).toNat ≤ H1.toNat) (a2 : H1.toNat + (C * 2#64 * 8#64).toNat ≤ H2.toNat)
    (a3 : H2.toNat + (C * 2#64).toNat ≤ H3.toNat) (a4 : H3.toNat + (C * 2#64 * 8#64).toNat ≤ H4.toNat)
    (a5 : H4.toNat + (C * 2#64 * 8#64).toNat ≤ H5.toNat) (e5 : H5.toNat ≤ 33806089496)
    (al0 : H0.toNat % 8 = 0) (al2 : H2.toNat % 8 = 0) (hK : K.toNat ≤ N.toNat) :
    HLay H5 T (GrowFoot T H0) KL SD (C * 2#64) K H0 H1 H2 H3 H4 (b + 1) ∧
      LayIn (fun x => H0.toNat ≤ x.toNat ∧ x.toNat < H5.toNat) (C * 2#64) SD H0 H1 H2 H3 H4 := by
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
  rw [c2sd] at a1; rw [c28] at a2 a4 a5; rw [c2] at a3
  have hp := lay.hdrP
  have cnt := lay.cnt
  have sd2 : C.toNat * 2 * SD.toNat = (C * 2#64).toNat * SD.toNat := by rw [c2]
  refine ⟨{ pow := by rw [c2,lay.pow]; ring
            fits := lay.fits
            sdAl := lay.sdAl
            ksAl := al0
            usAl := al2
            cnt := by rw [c2]; omega
            hdr := fun x lo hi => Or.inl ⟨lo,hi⟩
            hdrP := by omega
            eEnd := lay.eEnd
            fresh := fun x hx => Or.inr (by omega)
            keysR := ⟨by omega,by rw [← sd2]; omega,fun x lo _ => Or.inr (by omega)⟩
            valsR := ⟨by omega,by rw [c2]; omega,fun x lo _ => Or.inr (by omega)⟩
            usedR := ⟨by omega,by rw [c2]; omega,fun x lo _ => Or.inr (by omega)⟩
            orderR := ⟨by omega,by rw [c2]; omega,fun x lo _ => Or.inr (by omega)⟩
            oposR := ⟨by omega,by rw [c2]; omega,fun x lo _ => Or.inr (by omega)⟩ },?_⟩
  intro x hx
  unfold ArrOf at hx
  rw [← sd2,c2] at hx
  omega

set_option maxHeartbeats 4000000 in
/-- Heap-aware `htab_grow` from heap pointer `H0`: every word outside the footprint is kept in every outcome; a
return leaves the doubled layout whose five fresh arrays lie in `[H0, H5)` with `H5` at most the exit heap pointer,
valid against the precise footprint `GrowFoot T H0` (header plus heap from `H0`), header in memory and memory equal
to the entry memory outside that footprint. -/
theorem grow_aqmh (T : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) (H0 : BitVec 64) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun L M H => LK [(ofString "t",T)] L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0 ∧ H = H0)
      (fun _ _ _ => True)
      (fun _ M' H' => ∃ K NKS NVS NUS NOS NOPS H5 : BitVec 64, K.toNat ≤ N.toNat ∧ P0.toNat ≤ H0.toNat ∧
        H0.toNat ≤ H5.toNat ∧ H5.toNat ≤ H'.toNat ∧
        HLay H5 T (GrowFoot T H0) KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) ∧
        LayIn (fun x => H0.toNat ≤ x.toNat ∧ x.toNat < H5.toNat) (C * 2#64) SD NKS NVS NUS NOS NOPS ∧
        MI H5 T (GrowFoot T H0) M0 KL SD (C * 2#64) K NKS NVS NUS NOS NOPS M')
      (sourceFunctionBody Guest.guestFn_htab_grow) := by
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := lay.eEnd; omega
  have cHE : C.toNat ≤ 33806089496 := by have := arr_end lay.usedR lay.eEnd; omega
  have c2 : (C * 2#64).toNat = C.toNat * 2 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  have hwP : w.toNat < P0.toNat := by by_contra h; exact hw (lay.fresh w (by omega))
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_htab_grow,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aqmh_conseq (P := fun L M H => LK [(ofString "t",T)] L ∧ (Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0) ∧
    H = H0) ?_ (fun L M H h => ⟨h.1,⟨h.2.1,h.2.2.1⟩,h.2.2.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqmh_hdrDec (ofString "cap") 16#64 C (by lkne) (by simp) (fun M h => h.1.2.2.1) ?_
  refine aqmh_hdrDec (ofString "stride") 8#64 SD (by lkne) (by simp) (fun M h => h.1.2.1) ?_
  refine aqmh_hdrDec (ofString "keys") 32#64 KS (by lkne) (by simp) (fun M h => h.1.2.2.2.2.1) ?_
  refine aqmh_hdrDec (ofString "vals") 40#64 VS (by lkne) (by simp) (fun M h => h.1.2.2.2.2.2.1) ?_
  refine aqmh_hdrDec (ofString "order") 56#64 OS (by lkne) (by simp) (fun M h => h.1.2.2.2.2.2.2.2.1) ?_
  refine aqmh_hdrDec (ofString "nitems") 24#64 N (by lkne) (by simp) (fun M h => h.1.2.2.2.1) ?_
  refine aqmh_dec (Pb := fun L M H => LK (grP T C SD KS VS OS N) L ∧ (Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0) ∧
      H = H0) (Qb := fun _ _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s v H _ ⟨hl,hm⟩ _ ev _
    have hc := lk_get hl (ofString "cap") C (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,hc,panOpHOL,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨lk_cons hl _ _ (by lkne),hm⟩
  refine aqmh_allocDec (ofString "nkeys") _ (C * 2#64 * SD) H0 (by unfold grP; lkne) ?_ (fun p0 a1 _ _ al0 => ?_)
  · intro F s x hl ev
    have h1 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    have h2 := lk_get hl (ofString "stride") SD (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h1,h2,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  generalize allocationEnd H0 (C * 2#64 * SD) = H1 at *
  refine aqmh_allocDec (ofString "nvals") _ (C * 2#64 * 8#64) H1 (by unfold grP; lkne) ?_ (fun _ a2 _ _ _ => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h0,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  generalize allocationEnd H1 (C * 2#64 * 8#64) = H2 at *
  refine aqmh_allocDec (ofString "nused") _ (C * 2#64) H2 (by unfold grP; lkne) ?_ (fun _ a3 _ _ al2 => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,h0] at ev
    exact ev.symm
  generalize allocationEnd H2 (C * 2#64) = H3 at *
  refine aqmh_allocDec (ofString "norder") _ (C * 2#64 * 8#64) H3 (by unfold grP; lkne) ?_ (fun _ a4 _ _ _ => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h0,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  generalize allocationEnd H3 (C * 2#64 * 8#64) = H4 at *
  refine aqmh_allocDec (ofString "norder_pos") _ (C * 2#64 * 8#64) H4 (by unfold grP; lkne) ?_
    (fun _ a5 e5 _ _ => ?_)
  · intro F s x hl ev
    have h0 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    simp [EV,evalHOLExact,evalListHOLExact,h0,panOpHOL,valueIsWord,valueWord] at ev
    exact ev.symm
  generalize allocationEnd H4 (C * 2#64 * 8#64) = H5 at *
  have gl := fun K hK => grow_heapLay (H5 := H5) (K := K) lay p0 a1 a2 a3 a4 a5 e5 al0 al2 hK
  have hp := lay.hdrP
  have nC := lay.cnt
  have h12 : H1.toNat ≤ H2.toNat := by omega
  have hwG : ¬ Foot H5 T (GrowFoot T H0) w := by
    rintro (⟨lo,hi⟩ | h)
    · exact hw (lay.hdr w lo hi)
    · omega
  refine aqmh_conseq (aqmh_of_aqm (P := fun H L M => H = H5 ∧ LK ((ofString "norder_pos",H4) :: (ofString "norder",H3) ::
      (ofString "nused",H2) :: (ofString "nvals",H1) :: (ofString "nkeys",H0) :: grP T C SD KS VS OS N) L ∧
      MI H5 T (GrowFoot T H0) M0 KL SD C N KS VS US OS OPS M) (fun H _ => aqm_bound_eq
      (growTail_aqm T (GrowFoot T H0) KL SD C N KS VS US OS OPS H0 H1 H2 H3 H4 b M0 fitT cHE nC
        (fun x lo hi => Or.inl ⟨lo,hi⟩) hwG al2 (by omega) (by omega)
        (fun x lo hi => ⟨Or.inr (by omega),by omega⟩) (fun K hK => (gl K hK).1))))
    ?_ (fun _ _ _ _ => trivial) ?_
  · intro L M H ⟨hl,⟨hh,hm⟩,he⟩
    subst hm
    exact ⟨he,hl,hh,fun _ _ => rfl⟩
  · intro v M H' ⟨H,_,hle,e,K,hK,_,mi⟩
    subst e
    exact ⟨K,H0,H1,H2,H3,H4,H,hK,p0,by omega,hle,(gl K hK).1,(gl K hK).2,mi⟩

#print axioms aqmh_allocDec
#print axioms grow_heapLay
#print axioms grow_aqmh
end InitECandidate.Runtime
