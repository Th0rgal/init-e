import InitECandidate.Runtime.RecEcMulInitGD
import InitECandidate.Runtime.VmFn_ec_is_infinity
import InitECandidate.Runtime.VmFn_u256_bit
import InitECandidate.Runtime.VmFn_max
import InitECandidate.Runtime.VmFn_u256_bit_length
/-!
Window spec of the actual `ec_mul2(out, ...)`: the main loop doubles and adds into `[Out, Out + 96)` only (table
entries are read), the fresh 1536-byte table lies above the heap fence, and the heap is released back to the mark.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem tb_upd {H Out : BitVec 64} (n : MlS) (h1 : ofString "out" ≠ n) (h2 : ofString "table" ≠ n)
    (h3 : ofString "mark" ≠ n) (h4 : ofString "ax" ≠ n) (h5 : ofString "ay" ≠ n) (h6 : ofString "bx" ≠ n)
    (h7 : ofString "by" ≠ n) (L : GA) (v : ValueHOL 64) (h : TB H Out L) : TB H Out (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2.1,lu4_upd h4 _ _ h.2.2.2.1,lu4_upd h5 _ _ h.2.2.2.2.1,
    lu4_upd h6 _ _ h.2.2.2.2.2.1,lu4_upd h7 _ _ h.2.2.2.2.2.2⟩

theorem tb_res {H Out : BitVec 64} (n : MlS) (h1 : ofString "out" ≠ n) (h2 : ofString "table" ≠ n)
    (h3 : ofString "mark" ≠ n) (h4 : ofString "ax" ≠ n) (h5 : ofString "ay" ≠ n) (h6 : ofString "bx" ≠ n)
    (h7 : ofString "by" ≠ n) (L : GA) (o : Option (ValueHOL 64)) (h : TB H Out L) : TB H Out (L.resVarEq (n,o)) :=
  ⟨by rw [resVarEq_lookup_ne' _ _ _ _ h1]; exact h.1,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact h.2.1,
    by rw [resVarEq_lookup_ne' _ _ _ _ h3]; exact h.2.2.1,lu4_res h4 _ _ h.2.2.2.1,lu4_res h5 _ _ h.2.2.2.2.1,
    lu4_res h6 _ _ h.2.2.2.2.2.1,lu4_res h7 _ _ h.2.2.2.2.2.2⟩

section lp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A `TB`-keeping declaration (word local, name outside `TB`). -/
theorem decTB {H Out Lo Sc : BitVec 64} (n : MlS) (e : ExpHOL 64) {body : ProgHOL 64}
    (hn : ofString "out" ≠ n ∧ ofString "table" ≠ n ∧ ofString "mark" ≠ n ∧ ofString "ax" ≠ n ∧ ofString "ay" ≠ n ∧
      ofString "bx" ≠ n ∧ ofString "by" ≠ n)
    (hb : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G)
      (fun L _ G => TB H Out L ∧ RG Lo Sc G) RR body) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G)
      (fun L _ G => TB H Out L ∧ RG Lo Sc G) RR (.dec n .one e body) :=
  aqgd_dec (Pb := fun L _ G => TB H Out L ∧ RG Lo Sc G) (Qb := fun L _ G => TB H Out L ∧ RG Lo Sc G) _ _ _
    (fun h => h.elim) (fun s v H' _ hG ⟨tb,rg⟩ _ _ _ => by
      unfold GIs at hG; subst hG
      exact ⟨tb_upd n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 _ _ tb,rg⟩) hb
    (fun _ _ _ _ _ _ _ ⟨tb,rg⟩ => ⟨tb_res n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 _ _ tb,
      rg⟩)

/-- A `TB`-keeping declared call to a memory-and-globals-keeping callee. -/
theorem decCallTB {H Out Lo Sc : BitVec 64} (n f : MlS) (args : List (ExpHOL 64)) {body : ProgHOL 64}
    (params : List (MlS × ShapeHOL)) (body0 : ProgHOL 64) (rs0 : ShapeHOL)
    (inst : originalRuntimeCode.lookup f = some (params,body0,rs0)) (mf : MemoryFrame body0)
    (nb : noTopBreak body0 = true) (nc : noTopContinue body0 = true)
    (hn : ofString "out" ≠ n ∧ ofString "table" ≠ n ∧ ofString "mark" ≠ n ∧ ofString "ax" ≠ n ∧ ofString "ay" ≠ n ∧
      ofString "bx" ≠ n ∧ ofString "by" ≠ n)
    (hb : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G)
      (fun L _ G => TB H Out L ∧ RG Lo Sc G) RR body) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G)
      (fun L _ G => TB H Out L ∧ RG Lo Sc G) RR (.decCall n .one f args body) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ inst mf nb nc
    (fun L M G v ⟨tb,rg⟩ => ⟨tb_upd n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 _ _ tb,rg⟩)
    hb (fun _ _ _ _ _ _ _ ⟨tb,rg⟩ =>
      ⟨tb_res n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 _ _ tb,rg⟩)

theorem asgTB {H Out Lo Sc : BitVec 64} (n : MlS) (e : ExpHOL 64)
    (hn : ofString "out" ≠ n ∧ ofString "table" ≠ n ∧ ofString "mark" ≠ n ∧ ofString "ax" ≠ n ∧ ofString "ay" ≠ n ∧
      ofString "bx" ≠ n ∧ ofString "by" ≠ n) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G)
      (fun L _ G => TB H Out L ∧ RG Lo Sc G) RR (.assign .local n e) :=
  aqgd_assignLocal _ _ (fun s v _ _ ⟨tb,rg⟩ _ _ =>
    ⟨tb_upd n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 _ _ tb,rg⟩)

/-- One iteration of the `ec_mul2` main loop: two doublings of `out` and possibly an addition into `out` of a table
entry (read only). -/
theorem emLoop_wn (Lo Sc H Out : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oO : ¬ MWin Out 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G)
      (fun L _ G => TB H Out L ∧ RG Lo Sc G) RR emLoopBody := by
  unfold emLoopBody
  have hout : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), TB H Out s.locals →
      EV s (.var .local (ofString "out")) = some (.val (.word Out)) := fun s tb => by simp [EV,evalHOLExact,tb.1]
  have mfB : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_bit) :=
    memoryFrame_of_good vmLookup_u256_bit (by decide) (by decide)
  refine aqgd_seq (asgTB _ _ (by decide)) ?_
  refine aqgd_seq (tcDbl (LP := TB H Out) Lo Sc hw out 0 oO _ hout) ?_
  refine aqgd_seq (tcDbl (LP := TB H Out) Lo Sc hw out 0 oO _ hout) ?_
  refine decTB _ _ (by decide) ?_
  refine decCallTB _ _ _ _ _ _ vmLookup_u256_bit mfB (by body_check Guest.guestFn_u256_bit)
    (by body_check Guest.guestFn_u256_bit) (by decide) ?_
  refine decTB _ _ (by decide) ?_
  refine decCallTB _ _ _ _ _ _ vmLookup_u256_bit mfB (by body_check Guest.guestFn_u256_bit)
    (by body_check Guest.guestFn_u256_bit) (by decide) ?_
  refine aqgd_seq (asgTB _ _ (by decide)) ?_
  refine decCallTB _ _ _ _ _ _ vmLookup_u256_bit mfB (by body_check Guest.guestFn_u256_bit)
    (by body_check Guest.guestFn_u256_bit) (by decide) ?_
  refine decTB _ _ (by decide) ?_
  refine decCallTB _ _ _ _ _ _ vmLookup_u256_bit mfB (by body_check Guest.guestFn_u256_bit)
    (by body_check Guest.guestFn_u256_bit) (by decide) ?_
  refine aqgd_seq (asgTB _ _ (by decide)) ?_
  refine decTB _ _ (by decide) ?_
  refine aqgd_iteT _ ?_ aqgd_skip
  refine decTB _ _ (by decide) ?_
  refine decCallTB _ _ _ _ _ _ vmLookup_ec_is_infinity
    (memoryFrame_of_good vmLookup_ec_is_infinity (by decide) (by decide))
    (by body_check Guest.guestFn_ec_is_infinity) (by body_check Guest.guestFn_ec_is_infinity) (by decide) ?_
  exact aqgd_iteT _ (tcAA (LP := TB H Out) Lo Sc hw out hSc0 0 oO _ hout _ _ (fun s _ v ev => ev_load_u4 s _ v ev)
    (fun s _ v ev => ev_load_u4 s _ v ev)) aqgd_skip

#print axioms emLoop_wn

theorem aqgd_pureE {Φ : Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {A : GA → Prop} {Vn : MlS → Prop}
    (h : Φ → AQGD D B A w Vn P Q RR p) : AQGD D B A w Vn (fun L M G => P L M G ∧ Φ) Q RR p :=
  fun F s code dom aw sl H hH ⟨pre,φ⟩ => h φ F s code dom aw sl H hH pre

/-- The `ec_mul2` main loop and the heap release back to the mark `H`. -/
theorem emTail_wn (Lo Sc H Out : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oO : ¬ MWin Out 96 w) (hP0 : P0.toNat ≤ H.toNat) (hcapH : H.toNat ≤ 33806089496) (hal : H.toNat % 8 = 0)
    (hLoH : Lo.toNat ≤ H.toNat) {Q : GA → Mem → GA → Prop} :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => TB H Out L ∧ RG Lo Sc G) Q
      (fun _ _ G => RG Lo Sc G) emTail := by
  unfold emTail
  refine aqgd_dec (Pb := fun L _ G => TB H Out L ∧ RG Lo Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v H' _ hG ⟨tb,rg⟩ _ _ _ => by
      unfold GIs at hG; subst hG
      exact ⟨tb_upd _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ _ tb,rg⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_seq (aqgd_conseq (aqgd_whileBreak (I := fun L _ G => TB H Out L ∧ RG Lo Sc G) (C := fun _ _ _ => True)
    (Qb := fun _ _ _ => False) _ (fun _ _ _ _ _ _ _ _ => trivial)
    (aqgb_of_aqgd (aqgd_conseq (emLoop_wn Lo Sc H Out hw out hSc0 oO) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
      (fun _ _ _ h => h)))) (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)) ?_
  refine aqgd_seq (Q := fun _ _ G => HeapIs G H ∧ ScrIs Sc G) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0') ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (M' = M0' ∧ HeapIs G' H) ∧ OnlyHeap G0' G')
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' G0' _ => heapReleaseN_spec (SP0 := SP0) (G0 := G0) (FM := FM) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
      (D := D) (B := B) (w := w) M0' H hP0 hcapH hal G0') ?_ ?_) (aqgd_return _ ?_)
  · intro F s values callee rs _ H' hG ⟨tb,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,tb.2.2.1] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_heap_release_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩,rfl⟩
  · intro L M G v M' G' ⟨_,rg⟩ ⟨⟨_,hH⟩,oh⟩
    exact ⟨hH,scrIs_onlyHeap oh rg.2⟩
  · intro F s v _ _ _ ⟨hH,hsc⟩ _ _
    exact ⟨⟨H,hH,hLoH⟩,hsc⟩

#print axioms emTail_wn

/-- Locals of `ec_mul2` at entry: the output point and the four-word base coordinates. -/
def EM0 (Out : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out") = some (.val (.word Out)) ∧ LU4 (ofString "ax") L ∧ LU4 (ofString "ay") L ∧
    LU4 (ofString "bx") L ∧ LU4 (ofString "by") L

theorem em0u {Out : BitVec 64} (n : MlS) (h1 : ofString "out" ≠ n) (h4 : ofString "ax" ≠ n) (h5 : ofString "ay" ≠ n)
    (h6 : ofString "bx" ≠ n) (h7 : ofString "by" ≠ n) (L : GA) (v : ValueHOL 64) (h : EM0 Out L) :
    EM0 Out (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,lu4_upd h4 _ _ h.2.1,lu4_upd h5 _ _ h.2.2.1,lu4_upd h6 _ _ h.2.2.2.1,
    lu4_upd h7 _ _ h.2.2.2.2⟩

/-- The actual `ec_mul2(out, k1, ax, ay, k2, bx, by)`: writes only `[Out, Out + 96)`, its fresh table (released), the
accelerator scratch and released heap; keeps `RG`. -/
theorem ecMul2_wn (Lo Sc Out : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (hSc0 : Sc ≠ 0)
    (oO : ¬ MWin Out 96 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => EM0 Out L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun _ _ G => RG Lo Sc G) (sourceFunctionBody Guest.guestFn_ec_mul2) := by
  rw [emTop_eq]; unfold emTop
  have hout : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EM0 Out s.locals →
      EV s (.var .local (ofString "out")) = some (.val (.word Out)) := fun s h => by simp [EV,evalHOLExact,h.1]
  refine aqgd_seq (tcInf (LP := EM0 Out) Lo Sc 0 oO _ hout) ?_
  refine rdecMF (LP' := EM0 Out) (ofString "len1") _ _ _ _ _ _ vmLookup_u256_bit_length
    (memoryFrame_of_good vmLookup_u256_bit_length (by decide) (by decide))
    (by body_check Guest.guestFn_u256_bit_length) (by body_check Guest.guestFn_u256_bit_length)
    (fun L v h => em0u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ h) ?_
  refine rdecMF (LP' := EM0 Out) (ofString "len2") _ _ _ _ _ _ vmLookup_u256_bit_length
    (memoryFrame_of_good vmLookup_u256_bit_length (by decide) (by decide))
    (by body_check Guest.guestFn_u256_bit_length) (by body_check Guest.guestFn_u256_bit_length)
    (fun L v h => em0u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ h) ?_
  refine rdecMF (LP' := EM0 Out) (ofString "i") _ _ _ _ _ _ vmLookup_max
    (memoryFrame_of_good vmLookup_max (by decide) (by decide))
    (by body_check Guest.guestFn_max) (by body_check Guest.guestFn_max)
    (fun L v h => em0u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ h) ?_
  refine aqgd_seq (aqgd_iteT _ (retRG (LP := EM0 Out) Lo Sc _) aqgd_skip) ?_
  -- fix the heap pointer at the mark
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, (EM0 Out L ∧ HeapIs G H ∧ Lo.toNat ≤ H.toNat) ∧
      ScrIs Sc G) (Q := fun _ _ _ => False) ?_
    (fun _ _ _ ⟨h,⟨H,hH,le⟩,hsc⟩ => ⟨H,⟨h,hH,le⟩,hsc⟩) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0) ∧
    Lo.toNat ≤ H.toNat) (fun _ _ g aw ⟨⟨_,hH,le⟩,_⟩ => ⟨jws_heap_facts aw.1 hH,le⟩) ?_
  intro ⟨⟨hP0,hcapH,hal⟩,hLoH⟩
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((EM0 Out L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧ HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH,_⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨h,hH,_⟩,hsc⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨em0u _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ h,lookup_update_eq' _ _ _⟩,hH⟩,hsc⟩
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 1536#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (1536#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => (TB H Out L ∧ RG Lo Sc G) ∧ H.toNat + 1536 ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 1536#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,evalListHOLExact,panOpHOL,valueIsWord,valueWord] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨h,hm⟩,_⟩,hsc⟩ ⟨⟨ev,_,H',hH',c1,c2⟩,oh⟩ _
    subst ev
    have : (1536#64).toNat = 1536 := rfl
    refine ⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact h.1,lookup_update_eq' _ _ _,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hm,lu4_upd (by decide) _ _ h.2.1,lu4_upd (by decide) _ _ h.2.2.1,
      lu4_upd (by decide) _ _ h.2.2.2.1,lu4_upd (by decide) _ _ h.2.2.2.2⟩,⟨H',hH',by omega⟩,
      scrIs_onlyHeap oh hsc⟩,by omega⟩
  refine aqgd_pureE (fun hcap => ?_)
  exact emInit_wn Lo Sc H Out hw out hSc0 hal (by omega) hcap
    (emTail_wn Lo Sc H Out hw out hSc0 oO hP0 hcapH hal hLoH)

#print axioms ecMul2_wn
end lp
end InitECandidate.Runtime
