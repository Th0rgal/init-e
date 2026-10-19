import InitECandidate.Runtime.RlpDecodeArena
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.OriginalRlpUncheckedCode
import InitECandidate.Runtime.OriginalAllocationCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

theorem ev_op_word {F : Type} (s : PanSemStateFiniteExact 64 F) (o : BinOp) (es : List (ExpHOL 64)) (x : ValueHOL 64)
    (h : EV s (.op o es) = some x) : ∃ y : BitVec 64, x = .val (.word y) := by
  simp only [EV,evalHOLExact] at h
  split at h
  · split at h
    · obtain ⟨y,_,rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨y,rfl⟩
    · cases h
  · cases h

theorem resVar_lookup_ne (L : HolFiniteMapExact MlS (ValueHOL 64)) (x z : MlS) (o : Option (ValueHOL 64))
    (ne : z ≠ x) : (L.resVarEq (x,o)).lookup z = L.lookup z := by
  rw [lookup_resVarEq_toExact]
  cases o <;> simp [resVarHOLExact,ne]

/-- A successful word store wrote into the memory domain. -/
theorem store_none_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a : BitVec 64)
    (hd : EV s d = some (.val (.word a)))
    (hv : ∀ x, EV s v = some x → ∃ y : BitVec 64, x = .val (.word y))
    (h : (evaluateHOLFiniteState s (.store d v)).1 = none) : s.memaddrs a := by
  simp only [EV] at hd hv
  rw [evaluateHOLFiniteState_store,hd] at h
  dsimp only at h
  split at h
  · rename_i x hx
    obtain ⟨y,rfl⟩ := hv x hx
    split at h
    · rename_i m hm
      by_contra hn
      simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,hn] at hm
    · cases h
  · cases h

/-- A word store whose successful completion establishes `Q` from the domain bound of its address. -/
theorem aq_storeDom {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → P s.locals → SL Vn s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ a ∧ (a.toNat < 2^62 → Q s.locals))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, AW SP0 P0 FM G0 s.globals → P s.locals → SL Vn s.locals →
      EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQ SP0 P0 FM G0 w Vn P Q (.store d v) := by
  intro F s code dom aw sl pre
  obtain ⟨a,ha,ne,hq⟩ := hd s aw pre sl
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · aw pre sl)
  refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun e => ?_,?_,?_⟩
  · rw [loc]
    exact ⟨sl,hq (dom a (store_none_dom s d v a ha (hv s · aw pre sl) e))⟩
  all_goals rcases res with h | h <;> rw [h] <;> simp


theorem evalList_single {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (values : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e] = some values) :
    ∃ x, values = [x] ∧ EV s e = some x := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  cases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
  | none => simp [hx] at h
  | some x =>
    simp [hx,evalListHOLExact] at h
    exact ⟨x,h.symm,hx⟩

/-- After `arr = alloc(..)`: the array base is at or above `P0` and at most `HEAP_END`. -/
def SlA (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ a : BitVec 64, L.lookup (ofString "arr") = some (.val (.word a)) ∧ P0.toNat ≤ a.toNat ∧ a.toNat ≤ 33806089496

/-- Slices loop invariant: `arr + 16 i` does not wrap. -/
def SlJ (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ a i : BitVec 64, L.lookup (ofString "arr") = some (.val (.word a)) ∧ P0.toNat ≤ a.toNat ∧
    L.lookup (ofString "i") = some (.val (.word i)) ∧ a.toNat + 16 * i.toNat ≤ 2^62 + 16

/-- After the first slice store: its address was in the domain. -/
def SlJ' (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ a i : BitVec 64, L.lookup (ofString "arr") = some (.val (.word a)) ∧ P0.toNat ≤ a.toNat ∧
    L.lookup (ofString "i") = some (.val (.word i)) ∧ a.toNat + 16 * i.toNat < 2^62

theorem slice_addr0_toNat (a i : BitVec 64) (h : a.toNat + 16 * i.toNat ≤ 2^62 + 16) :
    (a + i * 16#64).toNat = a.toNat + 16 * i.toNat := by
  have h16 : (16#64).toNat = 16 := rfl
  have hi : i.toNat * 16 < 2^64 := by omega
  rw [BitVec.toNat_add,BitVec.toNat_mul,h16,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by omega)]
  omega

theorem slice_addr8_toNat (a i : BitVec 64) (h : a.toNat + 16 * i.toNat ≤ 2^62 + 16) :
    (a + (i * 16#64 + 8#64)).toNat = a.toNat + 16 * i.toNat + 8 := by
  have h16 : (16#64).toNat = 16 := rfl
  have h8 : (8#64).toNat = 8 := rfl
  have hi : i.toNat * 16 < 2^64 := by omega
  rw [BitVec.toNat_add,BitVec.toNat_add,BitVec.toNat_mul,h16,h8,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem slJ_update {P0 : BitVec 64} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : SlJ P0 L) (x : MlS) (v : ValueHOL 64)
    (h1 : x ≠ ofString "arr") (h2 : x ≠ ofString "i") : SlJ P0 (L.update (x,v)) := by
  obtain ⟨a,i,ha,lo,hi,hb⟩ := h
  exact ⟨a,i,by simp [HolFiniteMapExact.lookup_update,FUPDATE,ha]; exact fun e => absurd e h1,lo,
    by simp [HolFiniteMapExact.lookup_update,FUPDATE,hi]; exact fun e => absurd e h2,hb⟩

theorem slJ'_update {P0 : BitVec 64} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : SlJ' P0 L) (x : MlS)
    (v : ValueHOL 64) (h1 : x ≠ ofString "arr") (h2 : x ≠ ofString "i") : SlJ' P0 (L.update (x,v)) := by
  obtain ⟨a,i,ha,lo,hi,hb⟩ := h
  exact ⟨a,i,by simp [HolFiniteMapExact.lookup_update,FUPDATE,ha]; exact fun e => absurd e h1,lo,
    by simp [HolFiniteMapExact.lookup_update,FUPDATE,hi]; exact fun e => absurd e h2,hb⟩

/-- `rlp_list_to_slices` keeps every word below `P0` and outside the scratch arena in every outcome: the slice
array is a fresh heap block at or above `P0`, and each slice store address is non-wrapping because every earlier
slice store hit the (bounded) memory domain. -/
theorem rlpSlices_aq (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (hp : w.toNat < P0.toNat) :
    AQ SP0 P0 FM G0 w (fun _ => True) (fun _ => True) (fun _ => True)
      (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_list_to_slices,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aq_decCall (Pc := fun _ => True) (Qc := fun _ => True) _ _ _ _ _ _ _ originalRuntimeCode_rlpListCount_lookup
    (by simp) (rlpListCount_acallee hw) (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
    (fun _ _ _ _ => trivial)
  refine aq_decCall (Pc := SlA P0) (Qc := fun _ => True) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup
    (by simp) alloc_acallee (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s values callee post v code aw sl _ args lookup run _
    obtain ⟨_,_,⟨hpv,hhp,lo,hi,_⟩,_⟩ := aw
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    obtain ⟨n,rfl⟩ : ∃ n : BitVec 64, x = .val (.word n) := by
      simp only [EV,evalHOLExact] at ex
      split at ex
      · split at ex
        · obtain ⟨y,_,rfl⟩ := Option.map_eq_some_iff.mp ex
          exact ⟨y,rfl⟩
        · cases ex
      · cases ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    obtain ⟨_,_,ew,_⟩ := alloc_body_returned (callEntryStateHOLFinite s _) post hpv n code hhp
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) v run
    subst ew
    exact ⟨hpv,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi⟩
  refine aq_dec (Pb := fun L => SlA P0 L ∧ L.lookup (ofString "i") = some (.val (.word 0))) (Qb := fun _ => True)
    _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s v _ ⟨a,ha,lo,hi⟩ _ ev _
    simp [EV,evalHOLExact] at ev
    subst ev
    exact ⟨⟨a,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,ha],lo,hi⟩,
      by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩
  refine aq_dec (Pb := SlJ P0) (Qb := fun _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s v _ ⟨⟨a,ha,lo,hi⟩,h0⟩ _ _ _
    exact slJ_update ⟨a,0,ha,lo,h0,by simp; omega⟩ _ _ (by decide) (by decide)
  refine aq_seq (Q := SlJ P0) (aq_while (I := SlJ P0) (C := fun _ => True) _ (fun _ _ _ _ _ _ _ => trivial) ?_)
    (aq_return _)
  refine aq_decCall (Pc := SlJ P0) (Qc := SlJ P0) _ _ _ _ _ _ _ originalRuntimeCode_rlpUnchecked_lookup (by simp)
    (acallee_of_asafe (asafe_mf rlpUnchecked_memoryFrame)) (fun _ => rfl) ?_ ?_ ?_
  · intro F s _ _ _ v _ _ _ pre _ _ _ _
    exact slJ_update pre.1 _ _ (by decide) (by decide)
  · refine aq_seq (Q := SlJ' P0) (aq_storeDom _ _ ?_ ?_) (aq_seq (aq_store _ _ ?_ ?_)
      (aq_seq (aq_assignLocal (Q := SlJ' P0) _ _ ?_) (aq_assignLocal _ _ ?_)))
    · intro F s _ ⟨a,i,ha,lo,hi,hb⟩ _
      refine ⟨a + i * 16#64,?_,?_,fun lt => ⟨a,i,ha,lo,hi,?_⟩⟩
      · simp [EV,evalHOLExact,evalListHOLExact,ha,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
      · intro e
        have := slice_addr0_toNat a i hb
        rw [← e] at this
        omega
      · have := slice_addr0_toNat a i hb
        omega
    · intro F s x _ _ _ ev
      exact ev_op_word s _ _ x ev
    · intro F s _ ⟨a,i,ha,lo,hi,hb⟩ _
      refine ⟨a + (i * 16#64 + 8#64),?_,?_⟩
      · simp [EV,evalHOLExact,evalListHOLExact,ha,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
      · intro e
        have := slice_addr8_toNat a i (by omega)
        rw [← e] at this
        omega
    · intro F s x _ _ sl ev
      simp [EV,evalHOLExact] at ev
      exact sl _ trivial x ev
    · intro F s v _ pre _ _
      exact slJ'_update pre _ _ (by decide) (by decide)
    · intro F s v _ ⟨a,i,ha,lo,hi,hb⟩ _ ev
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      refine ⟨a,i + 1,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,ha],lo,
        by simp [HolFiniteMapExact.lookup_update,FUPDATE],?_⟩
      have : (i + 1).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
      omega
  · intro L L' _ h
    obtain ⟨a,i,ha,lo,hi,hb⟩ := h
    exact ⟨a,i,by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact ha,lo,
      by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hi,hb⟩

theorem rlpSlices_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (hp : w.toNat < P0.toNat) :
    ACallee SP0 P0 FM G0 w (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) :=
  acallee_of_aq (rlpSlices_aq hw hp)

#print axioms aq_storeDom
#print axioms rlpSlices_acallee
end InitECandidate.Runtime
