import InitECandidate.Runtime.PtMergeStepGD
/-!
The `merge_tx_into_block` storage loop (`mergeTailE`): the outer map `outer = lds(ts + 32)` has content at entry
(`TCont`) and lies outside every entry block region below the entry heap pointer, so it keeps its content through the
loop (`mlr_tc`); each iteration reads an item (`htab_item` on a `TCont` table, key aligned and bounded) and merges it
(`mergeInner_aqgd`); the loop keeps the storage-loop state.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Storage-loop invariant locals: `outer`, `bouter`, `cap`, a counter `i ≤ cap`. -/
def MLi (O BO N : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "outer") = some (.val (.word O)) ∧ L.lookup (ofString "bouter") = some (.val (.word BO)) ∧
  L.lookup (ofString "cap") = some (.val (.word N)) ∧
  ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat

section tc
variable {D : BitVec 64 → Prop} {B : Bool} {BO : BitVec 64} {lb0 : TLay} {R0 : Set (BitVec 64)}
  {Os0 : BitVec 64 → BitVec 64 → Prop} {H0 Nj : BitVec 64} {M0 : Mem}

/-- The outer map keeps its content in the storage-loop state. -/
theorem mlr_tc {O : BitVec 64} {lo : TLay} {R : Set (BitVec 64)} {M : Mem} {G : GA} (tc0 : TCont D B M0 O lo)
    (nc0 : lo.N.toNat < lo.C.toNat)
    (hOp : ∀ x, InTabF O lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      ¬ TabPhys BO lb0 x ∧ (∀ t ∈ R0, ¬ Os0 t x) ∧ x.toNat < H0.toNat)
    (mr : MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G) : TCont D B M O lo := by
  obtain ⟨_,_,_,_,_,_,_,_,_,fr⟩ := mr
  exact tc0.frame (Nat.le_of_lt nc0) (fun x hx => let ⟨a,b,c⟩ := hOp x hx; fr x a b c)
end tc

section it
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- One iteration `s = htab_item(outer, i); if s.0 != 0 { mergeInner }; i = i + 1` of the storage loop. -/
theorem mergeIter_aqgd (BO : BitVec 64) (lb0 : TLay) (R0 : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop)
    (H0 Nj : BitVec 64) (M0 : Mem) (O : BitVec 64) (lo : TLay) (tc0 : TCont D B M0 O lo) (kl0 : 20 ≤ lo.KL.toNat)
    (nc0 : lo.N.toNat < lo.C.toNat)
    (hOp : ∀ x, InTabF O lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      ¬ TabPhys BO lb0 x ∧ (∀ t ∈ R0, ¬ Os0 t x) ∧ x.toNat < H0.toNat)
    (hwB : ¬ TabPhys BO lb0 w) (hwO : ∀ t ∈ R0, ¬ Os0 t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (MLi O BO lo.N L ∧ ∃ R : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < lo.N.toNat)
      (fun L M G => MLi O BO lo.N L ∧ ∃ R : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G) RR mergeIter := by
  unfold mergeIter
  refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × Set (BitVec 64),
      (MLi O BO lo.N L ∧ L.lookup (ofString "i") = some (.val (.word q.1))) ∧
      (q.1.toNat < lo.N.toNat ∧ MLR D B BO lb0 R0 Os0 H0 Nj M0 q.2 M G))
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨⟨li,R,mr⟩,I,hi,hlt⟩ => ⟨(I,R),⟨li,hi⟩,hlt,mr⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  rcases q with ⟨I,R⟩
  refine aqgd_ghostR (fun M1 G1 ⟨hI,mr⟩ => ?_)
  change I.toNat < lo.N.toNat at hI
  have tc := mlr_tc tc0 nc0 hOp mr
  have tc' := tc
  obtain ⟨_,s',_,_,_,_,inv,_⟩ := tc'
  have endB := inv.endBound
  have hC : 2 ≤ lo.C.toNat := by omega
  have e1 : (I + 1).toNat = I.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  refine aqgd_decCall_htabItem_tc
    (LP := fun L => MLi O BO lo.N L ∧ L.lookup (ofString "i") = some (.val (.word I)))
    (Pc := fun L M G => (∃ b K vv : BitVec 64,
      MLs O BO lo.N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
        (K.toNat % 8 = 0 ∧ K.toNat + 52 ≤ 33806089496)) ∧
      MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G)
    (Qc := fun L M G => (∃ sv : ValueHOL 64, MLs O BO lo.N (I + 1) sv L) ∧
      ∃ R' : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R' M G)
    (ofString "s") (.var .local (ofString "outer")) (.var .local (ofString "i")) O I lo M1 G1 tc hI nc0 ?_
    (fun h => h.elim) ?_ ?_ ?_
  · intro F s _ _ _ ⟨⟨ho,_,_,_⟩,hi⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,ho,hi]
  · intro L b slot vv ⟨⟨ho,hbo,hcap,_⟩,hi⟩ sl _ _
    obtain ⟨k8,k52⟩ := item_key_ok inv kl0 hC sl
    exact ⟨⟨b,_,vv,⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,by rw [lookup_update_ne' _ _ (by decide)]; exact hbo,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hcap,by rw [lookup_update_ne' _ _ (by decide)]; exact hi,
      lookup_update_eq' _ _ _⟩,k8,k52⟩,mr⟩
  · refine aqgd_seq (Q := fun L M G => (∃ sv : ValueHOL 64, MLs O BO lo.N I sv L) ∧
        ∃ R' : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R' M G)
      (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
        (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_ ?_) ?_
    · refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64,
          (MLs O BO lo.N I (.rStruct [.val (.word q.1),.val (.word q.2.1),.val (.word q.2.2)]) L ∧
            MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G) ∧ (q.2.1.toNat % 8 = 0 ∧ q.2.1.toNat + 52 ≤ 33806089496))
        (aqgd_ex (fun q => ?_)) (fun L M G ⟨⟨⟨b,K,vv,lp,kk⟩,mr⟩,_⟩ => ⟨(b,K,vv),⟨lp,mr⟩,kk⟩) (fun _ _ _ h => h)
        (fun _ _ _ h => h)
      rcases q with ⟨b,K,vv⟩
      exact aqgd_pureE (fun ⟨k8,k52⟩ => aqgd_conseq (mergeInner_aqgd BO lb0 R0 Os0 H0 Nj M0 O lo.N I b K vv R hwB hwO
        hwP p0 Dall k8 k52) (fun _ _ _ h => h) (fun L M G ⟨lp,R',mr⟩ => ⟨⟨_,lp⟩,R',mr⟩) (fun _ _ _ h => h))
    · exact aqgd_conseq aqgd_skip (fun L M G ⟨⟨⟨b,K,vv,lp,_⟩,mr⟩,_⟩ => ⟨⟨_,lp⟩,R,mr⟩) (fun _ _ _ h => h)
        (fun _ _ _ h => h)
    · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨sv,ho,hbo,hcap,hi,hs⟩,R',mr⟩ _ ev => ?_)
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      exact ⟨⟨sv,by rw [lookup_update_ne' _ _ (by decide)]; exact ho,by rw [lookup_update_ne' _ _ (by decide)]; exact hbo,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hcap,lookup_update_eq' _ _ _,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hs⟩,R',mr⟩
  · intro L L' M' G' _ ⟨⟨sv,ho,hbo,hcap,hi,_⟩,R',mr⟩
    exact ⟨⟨by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact ho,by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hbo,
      by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hcap,I + 1,
      by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hi,by omega⟩,R',mr⟩

#print axioms mergeIter_aqgd
/-- The storage loop `while i < cap { mergeIter }`. -/
theorem mergeLoop_aqgd (BO : BitVec 64) (lb0 : TLay) (R0 : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop)
    (H0 Nj : BitVec 64) (M0 : Mem) (O : BitVec 64) (lo : TLay) (tc0 : TCont D B M0 O lo) (kl0 : 20 ≤ lo.KL.toNat)
    (nc0 : lo.N.toNat < lo.C.toNat)
    (hOp : ∀ x, InTabF O lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      ¬ TabPhys BO lb0 x ∧ (∀ t ∈ R0, ¬ Os0 t x) ∧ x.toNat < H0.toNat)
    (hwB : ¬ TabPhys BO lb0 w) (hwO : ∀ t ∈ R0, ¬ Os0 t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => MLi O BO lo.N L ∧ ∃ R : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G)
      (fun L M G => MLi O BO lo.N L ∧ ∃ R : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G) RR
      (.while mergeCond mergeIter) := by
  have tc0' := tc0
  obtain ⟨_,_,_,_,_,_,inv0,_⟩ := tc0'
  have endB := inv0.endBound
  refine aqgd_conseq (aqgd_whileE (C := fun L _ _ => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧
      I.toNat < lo.N.toNat) (E := fun _ _ _ => True) (Qb := fun _ _ _ => False) mergeCond ?_
      (fun _ _ _ _ _ _ _ _ => trivial)
      (aqgb_of_aqgd (mergeIter_aqgd BO lb0 R0 Os0 H0 Nj M0 O lo tc0 kl0 nc0 hOp hwB hwO hwP p0 Dall)))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim (fun h => h.1) False.elim) (fun _ _ _ h => h)
  intro F s x _ _ ⟨⟨_,_,hcap,I,hi,hle⟩,_⟩ _ ev hx
  unfold mergeCond at ev
  simp [EV,evalHOLExact,hi,hcap,slt_small (b := lo.N) (show I.toNat < 2 ^ 63 by omega)] at ev
  split at ev
  · rename_i h; exact ⟨I,hi,h.2⟩
  · exact absurd ev.symm hx

#print axioms mergeLoop_aqgd

/-- The storage loop with its entry declarations and `return 0` (`mergeTailE`), from the storage-loop state at entry
memory `M0` with `outer = lds(ts + 32)` a `TCont` table and `bouter = lds(bs + 32)`. -/
theorem mergeTail_aqgd (BO : BitVec 64) (lb0 : TLay) (R0 : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop)
    (H0 Nj : BitVec 64) (M0 : Mem) (O : BitVec 64) (lo : TLay) (tc0 : TCont D B M0 O lo) (kl0 : 20 ≤ lo.KL.toNat)
    (nc0 : lo.N.toNat < lo.C.toNat)
    (hOp : ∀ x, InTabF O lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      ¬ TabPhys BO lb0 x ∧ (∀ t ∈ R0, ¬ Os0 t x) ∧ x.toNat < H0.toNat)
    (hwB : ¬ TabPhys BO lb0 w) (hwO : ∀ t ∈ R0, ¬ Os0 t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (Ts Bs : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (dT : D (Ts + 32#64)) (cT : M0 (Ts + 32#64) = .word O) (dB : D (Bs + 32#64)) (cB : M0 (Bs + 32#64) = .word BO) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun _ M G => M = M0 ∧ MLR D B BO lb0 R0 Os0 H0 Nj M0 R0 M G) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ ∃ R : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G)
      mergeTailE := by
  have tc0' := tc0
  obtain ⟨_,s0,sm0,sd0,_,_,inv0,_⟩ := tc0'
  have hk := inv0.headerKeys; have kb := inv0.keysBefore; have ub := inv0.usedBefore; have ob := inv0.orderBefore
  have eb := inv0.endBound
  have e24 : (O + 24#64).toNat = O.toNat + 24 := by rw [BitVec.toNat_add]; simp; omega
  have dN : D (O + 24#64) := by
    rw [← sd0]; exact inv0.domain _ (by rw [e24]; have := inv0.tableAligned; omega) (by rw [e24]; omega)
      (by rw [e24]; omega)
  have cN : M0 (O + 24#64) = .word lo.N := by rw [← sm0]; exact inv0.cell24
  unfold mergeTailE
  refine aqgd_decD (Pb := fun L M G => L.lookup (ofString "outer") = some (.val (.word O)) ∧ M = M0 ∧
      MLR D B BO lb0 R0 Os0 H0 Nj M0 R0 M G) (Qb := fun _ _ _ => False) (ofString "outer") .one _ (fun h => h.elim)
    ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw dom hG ⟨hM,mr⟩ _ ev _
    unfold GIs at hG; subst hG
    obtain ⟨ets,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "ts") (by decide)
    unfold EV at ev
    rw [eval_record_word s .global _ Ts 32 O (eval_global_word s _ Ts (by rw [ets]; exact hTs))
      (by rw [dom.2.1]; exact dT) (by rw [hM]; exact cT)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨lookup_update_eq' _ _ _,hM,mr⟩
  refine aqgd_decD (Pb := fun L M G => (L.lookup (ofString "outer") = some (.val (.word O)) ∧
      L.lookup (ofString "bouter") = some (.val (.word BO))) ∧ M = M0 ∧ MLR D B BO lb0 R0 Os0 H0 Nj M0 R0 M G)
    (Qb := fun _ _ _ => False) (ofString "bouter") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw dom hG ⟨ho,hM,mr⟩ _ ev _
    unfold GIs at hG; subst hG
    obtain ⟨ebs,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "bs") (by decide)
    unfold EV at ev
    rw [eval_record_word s .global _ Bs 32 BO (eval_global_word s _ Bs (by rw [ebs]; exact hBs))
      (by rw [dom.2.1]; exact dB) (by rw [hM]; exact cB)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,lookup_update_eq' _ _ _⟩,hM,mr⟩
  refine aqgd_decD (Pb := fun L M G => (L.lookup (ofString "outer") = some (.val (.word O)) ∧
      L.lookup (ofString "bouter") = some (.val (.word BO)) ∧ L.lookup (ofString "cap") = some (.val (.word lo.N))) ∧
      MLR D B BO lb0 R0 Os0 H0 Nj M0 R0 M G)
    (Qb := fun _ _ _ => False) (ofString "cap") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw dom hG ⟨⟨ho,hbo⟩,hM,mr⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local _ O 24 lo.N (by simp [evalHOLExact,ho])
      (by rw [dom.2.1]; exact dN) (by rw [hM]; exact cN)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,by rw [lookup_update_ne' _ _ (by decide)]; exact hbo,
      lookup_update_eq' _ _ _⟩,mr⟩
  refine aqgd_decD (Pb := fun L M G => MLi O BO lo.N L ∧ ∃ R : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G)
    (Qb := fun _ _ _ => False) (ofString "i") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw dom hG ⟨⟨ho,hbo,hcap⟩,mr⟩ _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,by rw [lookup_update_ne' _ _ (by decide)]; exact hbo,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hcap,0#64,lookup_update_eq' _ _ _,by simp⟩,R0,mr⟩
  exact aqgd_seq (aqgd_conseq (mergeLoop_aqgd BO lb0 R0 Os0 H0 Nj M0 O lo tc0 kl0 nc0 hOp hwB hwO hwP p0 Dall)
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_return _ (fun s v H _ hG ⟨_,R,mr⟩ _ ev => by
      simp [EV,evalHOLExact] at ev; subst ev
      unfold GIs at hG; subst hG
      exact ⟨rfl,R,mr⟩))

#print axioms mergeTail_aqgd
end it
end InitECandidate.Runtime
