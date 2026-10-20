import InitECandidate.Runtime.RecHeapGD
/-!
Window specs of the actual `secp_accel_fp_pow4` / `secp_accel_fn_pow4` (shared shape `powBody`): they write only
their fresh 512-byte table at the entry heap pointer and the accelerator scratch, release the heap back to its entry
value, and keep `RG Lo Sc` (heap at or above `Lo`, `secp_accel_scratch = Sc`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The shared shape of `secp_accel_fp_pow4` / `secp_accel_fn_pow4` (multiplier `mulF`, squaring step `sq`). -/
def powBody (mulF : MlS) (sq : ProgHOL 64) : ProgHOL 64 :=
  (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "table") .one (ofString "alloc") [(.panop .mul [(.const 16),(.const 32)])] (.dec (ofString "t") (.comb [.one,.one,.one,.one]) (.var .local (ofString "a")) (.seq (.store (.op .add [(.var .local (ofString "table")),(.const 32)]) (.var .local (ofString "t"))) (.dec (ofString "d") .one (.const 2) (.seq (.while (.cmp .notLower (.const 15) (.var .local (ofString "d"))) (.seq (.call (some ((some (.local,ofString "t")),none)) mulF [(.var .local (ofString "t")),(.var .local (ofString "a"))]) (.seq (.store (.op .add [(.var .local (ofString "table")),(.panop .mul [(.var .local (ofString "d")),(.const 32)])]) (.var .local (ofString "t"))) (.assign .local (ofString "d") (.op .add [(.var .local (ofString "d")),(.const 1)]))))) (.dec (ofString "r") (.comb [.one,.one,.one,.one]) (.rstruct [(.const 1),(.const 0),(.const 0),(.const 0)]) (.dec (ofString "win") .one (.const 64) (.seq (.while (.cmp .lower (.const 0) (.var .local (ofString "win"))) (.seq (.assign .local (ofString "win") (.op .sub [(.var .local (ofString "win")),(.const 1)])) (.seq sq (.seq sq (.seq sq (.seq sq (.dec (ofString "limb") .one (.shift .lsr (.var .local (ofString "win")) (.const 4)) (.dec (ofString "shift") .one (.panop .mul [(.op .and [(.var .local (ofString "win")),(.const 15)]),(.const 4)]) (.dec (ofString "ew") .one (.rfield 0 (.var .local (ofString "e"))) (.seq (.ite (.cmp .equal (.var .local (ofString "limb")) (.const 1)) (.assign .local (ofString "ew") (.rfield 1 (.var .local (ofString "e")))) .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "limb")) (.const 2)) (.assign .local (ofString "ew") (.rfield 2 (.var .local (ofString "e")))) .skip) (.seq (.ite (.cmp .equal (.var .local (ofString "limb")) (.const 3)) (.assign .local (ofString "ew") (.rfield 3 (.var .local (ofString "e")))) .skip) (.dec (ofString "digit") .one (.op .and [(.shift .lsr (.var .local (ofString "ew")) (.var .local (ofString "shift"))),(.const 15)]) (.ite (.cmp .notEqual (.var .local (ofString "digit")) (.const 0)) (.call (some ((some (.local,ofString "r")),none)) mulF [(.var .local (ofString "r")),(.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "table")),(.panop .mul [(.var .local (ofString "digit")),(.const 32)])]))]) .skip)))))))))))))) (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.var .local (ofString "r")))))))))))))

def sqP : ProgHOL 64 :=
  (.call (some ((some (.local,ofString "r")),none)) (ofString "fp_sqr") [(.var .local (ofString "r"))])

def sqN : ProgHOL 64 :=
  (.call (some ((some (.local,ofString "r")),none)) (ofString "fn_mul") [(.var .local (ofString "r")),(.var .local (ofString "r"))])

theorem fpPow_eq : sourceFunctionBody Guest.guestFn_secp_accel_fp_pow4 = powBody (ofString "fp_mul") sqP := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp_accel_fp_pow4,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl

theorem fnPow_eq : sourceFunctionBody Guest.guestFn_secp_accel_fn_pow4 = powBody (ofString "fn_mul") sqN := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_secp_accel_fn_pow4,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  try rfl


theorem lu4_res {x n : MlS} (h : x ≠ n) (L : GA) (o : Option (ValueHOL 64)) (hx : LU4 x L) :
    LU4 x (L.resVarEq (n,o)) :=
  let ⟨u,hu,uu⟩ := hx; ⟨u,by rw [resVarEq_lookup_ne' _ _ _ _ h]; exact hu,uu⟩

theorem ne_of_toNat_lt {w a : BitVec 64} (h : w.toNat < a.toNat) : w ≠ a := fun e => by subst e; omega

/-- The globals invariant of the recovery frame: heap pointer at or above `Lo`, accelerator scratch at `Sc`. -/
def RG (Lo Sc : BitVec 64) (G : GA) : Prop := HGe Lo G ∧ ScrIs Sc G

section rc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `x = f(e1, e2)` for a four-word multiplier `f`. -/
theorem rcallMul {LP : GA → Prop} (Sc : BitVec 64) (callee0 : MlS) (body0 : ProgHOL 64)
    (inst : originalRuntimeCode.lookup callee0 = some ([(ofString "a",.comb [.one,.one,.one,.one]),
      (ofString "b",.comb [.one,.one,.one,.one])],body0,.comb [.one,.one,.one,.one]))
    (hmul : AQGD D B A w (fun _ => False) (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) body0)
    (x : MlS) (e1 e2 : ExpHOL 64)
    (he1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v, EV s e1 = some v → U4V v)
    (he2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v, EV s e2 = some v → U4V v)
    (hup : ∀ L v, LP L → U4V v → LP (L.update (x,v))) :
    AQGD D B A w (fun _ => False) (fun L _ G => LP L ∧ ScrIs Sc G) (fun L _ G => LP L ∧ ScrIs Sc G) RR
      (.call (some (some (.local,x),none)) callee0 [e1,e2]) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
    (RRe := fun _ _ _ r _ G => U4V r ∧ ScrIs Sc G) _ _ _ _ _ _ inst (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ _ _ _ => hmul)
    (fun s values callee rs _ H hG ⟨lp,hsc⟩ _ args lookup => by
      unfold GIs at hG; subst hG
      obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
      obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
      have := evalList_nil' s _ r2; subst this
      have e := callee_eq inst lookup
      exact ⟨⟨⟨v1,by rw [e]; simp (config := {decide := true}),he1 s lp v1 ev1⟩,
        ⟨v2,by rw [e]; simp (config := {decide := true}),he2 s lp v2 ev2⟩⟩,hsc⟩)
    (fun L _ _ v _ _ ⟨lp,_⟩ ⟨uv,hsc⟩ => ⟨hup L v lp uv,hsc⟩)

#print axioms rcallMul
end rc
/-- Locals of the exponentiation: base `a`, heap mark and table at `H` (with room for the 512-byte table). -/
def PBc (H : BitVec 64) (L : GA) : Prop :=
  (LU4 (ofString "a") L ∧ L.lookup (ofString "mark") = some (.val (.word H)) ∧
    L.lookup (ofString "table") = some (.val (.word H))) ∧ H.toNat + 512 ≤ 33806089496

theorem pbc_upd {H : BitVec 64} {n : MlS} (h1 : ofString "a" ≠ n) (h2 : ofString "mark" ≠ n)
    (h3 : ofString "table" ≠ n) (L : GA) (v : ValueHOL 64) (h : PBc H L) : PBc H (L.update (n,v)) :=
  ⟨⟨lu4_upd h1 _ _ h.1.1,by rw [lookup_update_ne' _ _ h2]; exact h.1.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.1.2.2⟩,h.2⟩

theorem pbc_res {H : BitVec 64} {n : MlS} (h1 : ofString "a" ≠ n) (h2 : ofString "mark" ≠ n)
    (h3 : ofString "table" ≠ n) (L : GA) (o : Option (ValueHOL 64)) (h : PBc H L) : PBc H (L.resVarEq (n,o)) :=
  ⟨⟨lu4_res h1 _ _ h.1.1,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact h.1.2.1,
    by rw [resVarEq_lookup_ne' _ _ _ _ h3]; exact h.1.2.2⟩,h.2⟩

theorem toNat_addK {H : BitVec 64} {k : Nat} (h : H.toNat + k < 2 ^ 64) :
    (H + BitVec.ofNat 64 k).toNat = H.toNat + k := by
  simp [BitVec.toNat_add]; omega

section pw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The shared exponentiation `powBody mulF sq` writes only its fresh 512-byte table at the heap pointer, the
accelerator scratch (through `mulF` / `sq`), and releases the heap back to its entry value. -/
theorem pow_wn (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) (mulF : MlS)
    (body0 : ProgHOL 64)
    (inst : originalRuntimeCode.lookup mulF = some ([(ofString "a",.comb [.one,.one,.one,.one]),
      (ofString "b",.comb [.one,.one,.one,.one])],body0,.comb [.one,.one,.one,.one]))
    (hmul : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => (LU4 (ofString "a") L ∧ LU4 (ofString "b") L) ∧ ScrIs Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ ScrIs Sc G) body0)
    (sq : ProgHOL 64)
    (hsq : ∀ (LP : GA → Prop) (RR' : ValueHOL 64 → Mem → GA → Prop),
      (∀ L v, LP L → U4V v → LP (L.update (ofString "r",v))) → (∀ L, LP L → LU4 (ofString "r") L) →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LP L ∧ ScrIs Sc G)
        (fun L _ G => LP L ∧ ScrIs Sc G) RR' sq) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (powBody mulF sq) := by
  refine aqgd_conseq (P := fun L _ G => ∃ H : BitVec 64, (LU4 (ofString "a") L ∧ HeapIs G H ∧
      Lo.toNat ≤ H.toNat) ∧ ScrIs Sc G) (Q := fun _ _ _ => True) ?_
    (fun _ _ _ ⟨ha,⟨H,hH,le⟩,hsc⟩ => ⟨H,⟨ha,hH,le⟩,hsc⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_exE (fun H => ?_)
  refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0) ∧
    Lo.toNat ≤ H.toNat) (fun _ _ g aw ⟨⟨_,hH,le⟩,_⟩ => ⟨jws_heap_facts aw.1 hH,le⟩) ?_
  intro ⟨⟨hP0,hcapH,hal⟩,hLoH⟩
  unfold powBody
  -- mark = heap_mark()
  refine aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => ((LU4 (ofString "a") L ∧ L.lookup (ofString "mark") = some (.val (.word H))) ∧
      HeapIs G H) ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup
    (fun _ M0' G0' ⟨⟨_,hH,_⟩,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ha,hH,_⟩,hsc⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨⟨⟨lu4_upd (by decide) _ _ ha,lookup_update_eq' _ _ _⟩,hH⟩,hsc⟩
  -- table = alloc(16 * 32)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word 512#64)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + (512#64).toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L _ G => PBc H L ∧ ScrIs Sc G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) 512#64 H M0' G0') ?_ (fun h => h.elim) ?_ ?_
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
  · intro L M G v M' G' ⟨⟨⟨ha,hm⟩,_⟩,hsc⟩ ⟨⟨ev,_,H',_,c1,c2⟩,oh⟩ _
    subst ev
    have : (512#64).toNat = 512 := rfl
    exact ⟨⟨⟨lu4_upd (by decide) _ _ ha,by rw [lookup_update_ne' _ _ (by decide)]; exact hm,lookup_update_eq' _ _ _⟩,
      by omega⟩,scrIs_onlyHeap oh hsc⟩
  have tadd : ∀ k : Nat, k < 512 → (H + BitVec.ofNat 64 k).toNat = H.toNat + k := fun k hk =>
    toNat_addK (by omega)
  -- t = a
  let T1 := fun L : GA => PBc H L ∧ LU4 (ofString "t") L
  refine aqgd_dec (Pb := fun L _ G => T1 L ∧ ScrIs Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H' _ hG ⟨pb,hsc⟩ _ ev _
    unfold GIs at hG; subst hG
    obtain ⟨u,hu,uu⟩ := pb.1.1
    simp [EV,evalHOLExact,hu] at ev; subst ev
    exact ⟨⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,u,lookup_update_eq' _ _ _,uu⟩,hsc⟩
  -- st table + 32, t
  refine aqgd_seq (aqgd_storeK (LP := fun L G => T1 L ∧ ScrIs Sc G) (LQ := fun L G => T1 L ∧ ScrIs Sc G) _ _
    (fun s _ ⟨⟨pb,ht⟩,hsc⟩ => ⟨H + 32#64,4,
      by simp [EV,evalHOLExact,evalListHOLExact,pb.1.2.2,wordOpHOL,wordOp,valueIsWord,valueWord],
      ev_var_u4 s _ ht,fun j hj => ne_of_toNat_lt (by
        rw [ofNat_add_add,tadd _ (by omega)]; omega),⟨pb,ht⟩,hsc⟩)) ?_
  -- d = 2; fill loop
  let T2 := fun L : GA => T1 L ∧ ∃ Dd : BitVec 64, L.lookup (ofString "d") = some (.val (.word Dd))
  refine aqgd_dec (Pb := fun L _ G => T2 L ∧ ScrIs Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H' _ hG ⟨⟨pb,ht⟩,hsc⟩ _ ev _
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,lu4_upd (by decide) _ _ ht⟩,_,
      lookup_update_eq' _ _ _⟩,hsc⟩
  refine aqgd_seq (aqgd_conseq (aqgd_whileBreak (I := fun L _ G => T2 L ∧ ScrIs Sc G)
    (C := fun L _ _ => ∃ Dd : BitVec 64, L.lookup (ofString "d") = some (.val (.word Dd)) ∧ Dd.toNat ≤ 15)
    (Qb := fun _ _ _ => False) _ ?_ (aqgb_of_aqgd ?_)) (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim)
    (fun _ _ _ h => h)) ?_
  · intro F s x _ _ ⟨⟨_,Dd,hd⟩,_⟩ _ ev nz
    simp [EV,evalHOLExact,hd,Compiler.Encoders.Asm.wordCmpHOL] at ev
    by_cases h : Dd ≤ 15#64
    · exact ⟨Dd,hd,BitVec.le_def.mp h⟩
    · rw [if_neg h] at ev; exact absurd ev.symm nz
  · let T3 := fun L : GA => T1 L ∧ ∃ Dd : BitVec 64, L.lookup (ofString "d") = some (.val (.word Dd)) ∧
      Dd.toNat ≤ 15
    refine aqgd_conseq (P := fun L _ G => T3 L ∧ ScrIs Sc G) ?_ (fun _ _ _ ⟨⟨⟨t1,_⟩,hsc⟩,c⟩ => ⟨⟨t1,c⟩,hsc⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_seq (rcallMul (LP := T3) Sc _ _ inst hmul _ _ _ (fun s ⟨⟨_,ht⟩,_⟩ v ev => by
        obtain ⟨u,hu,uu⟩ := ht; simp [EV,evalHOLExact,hu] at ev; subst ev; exact uu)
      (fun s ⟨⟨pb,_⟩,_⟩ v ev => by
        obtain ⟨u,hu,uu⟩ := pb.1.1; simp [EV,evalHOLExact,hu] at ev; subst ev; exact uu)
      (fun L v ⟨⟨pb,_⟩,Dd,hd,hle⟩ uv => ⟨⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,_,
        lookup_update_eq' _ _ _,uv⟩,Dd,by rw [lookup_update_ne' _ _ (by decide)]; exact hd,hle⟩)) ?_
    refine aqgd_seq (aqgd_storeK (LP := fun L G => T3 L ∧ ScrIs Sc G) (LQ := fun L G => T3 L ∧ ScrIs Sc G) _ _
      (fun s _ ⟨⟨⟨pb,ht⟩,Dd,hd,hle⟩,hsc⟩ => ⟨H + Dd * 32#64,4,
        by simp [EV,evalHOLExact,evalListHOLExact,pb.1.2.2,hd,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL],
        ev_var_u4 s _ ht,fun j hj => ne_of_toNat_lt (by
          have e1 : (Dd * 32#64).toNat = Dd.toNat * 32 := by simp [BitVec.toNat_mul]; omega
          have e2 : H + Dd * 32#64 = H + BitVec.ofNat 64 (Dd.toNat * 32) := by
            congr 1 <;> (apply BitVec.eq_of_toNat_eq; rw [e1]; simp)
          rw [e2,ofNat_add_add,tadd _ (by omega)]; omega),⟨⟨pb,ht⟩,Dd,hd,hle⟩,hsc⟩)) ?_
    refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨pb,ht⟩,_⟩,hsc⟩ _ ev => ?_)
    obtain ⟨y,rfl⟩ := isWord_op s _ _ v ev
    exact ⟨⟨⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,lu4_upd (by decide) _ _ ht⟩,_,
      lookup_update_eq' _ _ _⟩,hsc⟩
  -- r = 1
  let R1 := fun L : GA => PBc H L ∧ LU4 (ofString "r") L
  have r1u : ∀ (n : MlS), ofString "a" ≠ n → ofString "mark" ≠ n → ofString "table" ≠ n → ofString "r" ≠ n →
      ∀ L v, R1 L → R1 (L.update (n,v)) := fun n h1 h2 h3 h4 L v ⟨pb,hr⟩ =>
    ⟨pbc_upd h1 h2 h3 L v pb,lu4_upd h4 L v hr⟩
  have r1r : ∀ (n : MlS), ofString "a" ≠ n → ofString "mark" ≠ n → ofString "table" ≠ n → ofString "r" ≠ n →
      ∀ L o, R1 L → R1 (L.resVarEq (n,o)) := fun n h1 h2 h3 h4 L o ⟨pb,hr⟩ =>
    ⟨pbc_res h1 h2 h3 L o pb,lu4_res h4 L o hr⟩
  refine aqgd_dec (Pb := fun L _ G => R1 L ∧ ScrIs Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H' _ hG ⟨⟨⟨pb,_⟩,_⟩,hsc⟩ _ ev _
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,evalListHOLExact] at ev; subst ev
    exact ⟨⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,_,lookup_update_eq' _ _ _,u4_of_vals _ _ _ _⟩,hsc⟩
  have decR : ∀ (n : MlS) (e : ExpHOL 64) {body : ProgHOL 64} {RR' : ValueHOL 64 → Mem → GA → Prop},
      ofString "a" ≠ n → ofString "mark" ≠ n → ofString "table" ≠ n → ofString "r" ≠ n →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => R1 L ∧ ScrIs Sc G)
        (fun L _ G => R1 L ∧ ScrIs Sc G) RR' body →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => R1 L ∧ ScrIs Sc G)
        (fun L _ G => R1 L ∧ ScrIs Sc G) RR' (.dec n .one e body) :=
    fun n e body RR' h1 h2 h3 h4 hb => aqgd_dec (Pb := fun L _ G => R1 L ∧ ScrIs Sc G)
      (Qb := fun L _ G => R1 L ∧ ScrIs Sc G) _ _ _ (fun h => h.elim)
      (fun s v H' _ hG ⟨r1,hsc⟩ _ _ _ => by
        unfold GIs at hG; subst hG; exact ⟨r1u n h1 h2 h3 h4 _ _ r1,hsc⟩) hb
      (fun L _ _ L' _ _ _ ⟨r1,hsc⟩ => ⟨r1r n h1 h2 h3 h4 _ _ r1,hsc⟩)
  have asR : ∀ (n : MlS) (e : ExpHOL 64) {RR' : ValueHOL 64 → Mem → GA → Prop},
      ofString "a" ≠ n → ofString "mark" ≠ n → ofString "table" ≠ n → ofString "r" ≠ n →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => R1 L ∧ ScrIs Sc G)
        (fun L _ G => R1 L ∧ ScrIs Sc G) RR' (.assign .local n e) :=
    fun n e RR' h1 h2 h3 h4 => aqgd_assignLocal _ _ (fun s v _ _ ⟨r1,hsc⟩ _ _ => ⟨r1u n h1 h2 h3 h4 _ _ r1,hsc⟩)
  have hsqR := fun (RR' : ValueHOL 64 → Mem → GA → Prop) => hsq R1 RR'
    (fun L v ⟨pb,_⟩ uv => ⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,_,lookup_update_eq' _ _ _,uv⟩)
    (fun L ⟨_,hr⟩ => hr)
  -- win = 64; square-and-multiply loop
  refine aqgd_dec (Pb := fun L _ G => R1 L ∧ ScrIs Sc G) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim)
    (fun s v H' _ hG ⟨r1,hsc⟩ _ _ _ => by
      unfold GIs at hG; subst hG; exact ⟨r1u _ (by decide) (by decide) (by decide) (by decide) _ _ r1,hsc⟩) ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  refine aqgd_seq (aqgd_conseq (aqgd_whileBreak (I := fun L _ G => R1 L ∧ ScrIs Sc G) (C := fun _ _ _ => True)
    (Qb := fun _ _ _ => False) _ (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd ?_)) (fun _ _ _ h => h)
    (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)) ?_
  · refine aqgd_conseq (P := fun L _ G => R1 L ∧ ScrIs Sc G) ?_ (fun _ _ _ ⟨h,_⟩ => h) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
    refine aqgd_seq (asR (ofString "win") _ (by decide) (by decide) (by decide) (by decide)) ?_
    refine aqgd_seq (hsqR _) (aqgd_seq (hsqR _) (aqgd_seq (hsqR _) (aqgd_seq (hsqR _) ?_)))
    refine decR (ofString "limb") _ (by decide) (by decide) (by decide) (by decide) ?_
    refine decR (ofString "shift") _ (by decide) (by decide) (by decide) (by decide) ?_
    refine decR (ofString "ew") _ (by decide) (by decide) (by decide) (by decide) ?_
    refine aqgd_seq (aqgd_iteT _ (asR (ofString "ew") _ (by decide) (by decide) (by decide) (by decide)) aqgd_skip) ?_
    refine aqgd_seq (aqgd_iteT _ (asR (ofString "ew") _ (by decide) (by decide) (by decide) (by decide)) aqgd_skip) ?_
    refine aqgd_seq (aqgd_iteT _ (asR (ofString "ew") _ (by decide) (by decide) (by decide) (by decide)) aqgd_skip) ?_
    refine decR (ofString "digit") _ (by decide) (by decide) (by decide) (by decide) ?_
    refine aqgd_iteT _ ?_ aqgd_skip
    exact rcallMul (LP := R1) Sc _ _ inst hmul _ _ _
      (fun s ⟨_,hr⟩ v ev => by obtain ⟨u,hu,uu⟩ := hr; simp [EV,evalHOLExact,hu] at ev; subst ev; exact uu)
      (fun s _ v ev => ev_load_u4 s _ v ev)
      (fun L v ⟨pb,_⟩ uv => ⟨pbc_upd (by decide) (by decide) (by decide) _ _ pb,_,lookup_update_eq' _ _ _,uv⟩)
  -- heap_release(mark); return r
  refine aqgd_seq (Q := fun L _ G => LU4 (ofString "r") L ∧ HeapIs G H ∧ ScrIs Sc G) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0') ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (M' = M0' ∧ HeapIs G' H) ∧ OnlyHeap G0' G')
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' G0' _ => heapReleaseN_spec (SP0 := SP0) (G0 := G0) (FM := FM) (J := J) (C := C) (SKB := SKB) (Nj := Nj)
      (D := D) (B := B) (w := w) M0' H hP0 hcapH hal G0') ?_ ?_) (aqgd_return _ ?_)
  · intro F s values callee rs _ H' hG ⟨⟨pb,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,pb.1.2.1] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_heap_release_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨_,hr⟩,hsc⟩ ⟨⟨_,hH⟩,oh⟩
    exact ⟨hr,hH,scrIs_onlyHeap oh hsc⟩
  · intro F s v _ _ _ ⟨⟨u,hu,uu⟩,hH,hsc⟩ _ ev
    simp [EV,evalHOLExact,hu] at ev; subst ev
    exact ⟨uu,⟨H,hH,hLoH⟩,hsc⟩

#print axioms pow_wn

theorem fpPow4_wn (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_secp_accel_fp_pow4) := by
  rw [fpPow_eq]
  refine pow_wn Lo Sc hw out _ _ vmLookup_fp_mul (fpMul_wn Sc out) sqP (fun LP RR' hup hlu => ?_)
  unfold sqP
  exact aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => LU4 (ofString "a") L ∧ ScrIs Sc G)
    (RRe := fun _ _ _ r _ G => U4V r ∧ ScrIs Sc G) _ _ _ _ _ _ vmLookup_fp_sqr (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ _ _ _ => fpSqr_wn Sc out)
    (fun s values callee rs _ H hG ⟨lp,hsc⟩ _ args lookup => by
      unfold GIs at hG; subst hG
      obtain ⟨u,hu,uu⟩ := hlu _ lp
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hu] at args
      subst args
      have e := callee_eq vmLookup_fp_sqr lookup
      exact ⟨⟨u,by rw [e]; simp,uu⟩,hsc⟩)
    (fun L _ _ v _ _ ⟨lp,_⟩ ⟨uv,hsc⟩ => ⟨hup L v lp uv,hsc⟩)

theorem fnPow4_wn (Lo Sc : BitVec 64) (hw : w.toNat < Lo.toNat) (out : ¬ MWin Sc 448 w) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun L _ G => LU4 (ofString "a") L ∧ RG Lo Sc G)
      (fun _ _ _ => True) (fun r _ G => U4V r ∧ RG Lo Sc G) (sourceFunctionBody Guest.guestFn_secp_accel_fn_pow4) := by
  rw [fnPow_eq]
  refine pow_wn Lo Sc hw out _ _ vmLookup_fn_mul (fnMul_wn Sc out) sqN (fun LP RR' hup hlu => ?_)
  unfold sqN
  have he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ v,
      EV s (.var .local (ofString "r")) = some v → U4V v := fun s lp v ev => by
    obtain ⟨u,hu,uu⟩ := hlu _ lp; simp [EV,evalHOLExact,hu] at ev; subst ev; exact uu
  exact rcallMul (LP := LP) Sc _ _ vmLookup_fn_mul (fnMul_wn Sc out) _ _ _ he he hup

#print axioms fnPow4_wn
end pw
end InitECandidate.Runtime
