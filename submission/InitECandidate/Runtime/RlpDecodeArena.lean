import InitECandidate.Runtime.RlpValidateArena
import InitECandidate.Runtime.OriginalRlpItemTotalCode
import InitECandidate.Runtime.OriginalRlpListCountCode
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.OriginalRlpDecodeFullyCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {Vn : MlS → Prop}

theorem aqT_skip : AQT SP0 P0 FM w Vn .skip := by unfold AQT; exact aq_skip

theorem aqT_call (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM w body) :
    AQT SP0 P0 FM w Vn (.call (some (none,none)) function arguments) := by
  unfold AQT; exact aq_call function arguments parameters body returnShape installed allOne hb

theorem acallee_of_aqT {Vn' : MlS → Prop} {body : ProgHOL 64} (h : AQT SP0 P0 FM w Vn' body) :
    ACallee SP0 P0 FM w body := by
  unfold AQT at h; exact acallee_of_aq h

/-- `rlp_item_total` keeps every word outside the scratch arena in every outcome. -/
theorem rlpItemTotal_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ACallee SP0 P0 FM w (sourceFunctionBody Guest.guestFn_rlp_item_total) := by
  refine acallee_of_aqT (Vn' := fun x => x ≠ ofString "h") ?_
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact fun _ => rfl
    | exact fun hn => absurd rfl hn
    | exact aqT_assignLocal _ _
    | exact aqT_return _
    | exact aqT_skip
    | exact aqT_call _ _ _ _ _ originalRuntimeCode_rlpValidation_lookup (by simp) (rlpValidate_acallee hw)
    | apply aqT_seq
    | apply aqT_while
    | apply aqT_ite
    | apply aqT_dec
    | refine aqT_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpHeader_lookup (by simp)
        (acallee_of_asafe (asafe_mf rlpHeader_memoryFrame)) ?_ ?_

/-- `rlp_list_count` keeps every word outside the scratch arena in every outcome. -/
theorem rlpListCount_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ACallee SP0 P0 FM w (sourceFunctionBody Guest.guestFn_rlp_list_count) := by
  refine acallee_of_aqT (Vn' := fun _ => True) ?_
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact fun _ => rfl
    | exact aqT_assignLocal _ _
    | exact aqT_return _
    | exact aqT_skip
    | apply aqT_seq
    | apply aqT_while
    | apply aqT_ite
    | apply aqT_dec
    | refine aqT_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpItemTotal_lookup (by simp)
        (rlpItemTotal_acallee hw) ?_ ?_

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `rlp_item` keeps every word outside the scratch arena in every outcome. -/
theorem rlpItem_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ACallee SP0 P0 FM w (sourceFunctionBody Guest.guestFn_rlp_item) := by
  refine acallee_of_aqT (Vn' := fun _ => True) ?_
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact fun _ => rfl
    | exact aqT_assignLocal _ _
    | exact aqT_return _
    | exact aqT_skip
    | exact aqT_call _ _ _ _ _ originalRuntimeCode_rlpFail_lookup (by simp)
        (acallee_of_asafe (asafe_mf rlpFail_memoryFrame))
    | exact aqT_call _ _ _ _ _ originalRuntimeCode_rlpListCount_lookup (by simp) (rlpListCount_acallee hw)
    | apply aqT_seq
    | apply aqT_while
    | apply aqT_ite
    | apply aqT_dec
    | refine aqT_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpReadLength_lookup (by simp)
        (acallee_of_asafe (asafe_mf rlpReadLength_memoryFrame)) ?_ ?_

/-- `rlp_decode_fully` keeps every word outside the scratch arena in every outcome. -/
theorem rlpDecodeFully_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ACallee SP0 P0 FM w (sourceFunctionBody Guest.guestFn_rlp_decode_fully) := by
  refine acallee_of_aqT (Vn' := fun x => x ≠ ofString "it") ?_
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact fun _ => rfl
    | exact fun hn => absurd rfl hn
    | exact aqT_assignLocal _ _
    | exact aqT_return _
    | exact aqT_skip
    | exact aqT_call _ _ _ _ _ originalRuntimeCode_rlpFail_lookup (by simp)
        (acallee_of_asafe (asafe_mf rlpFail_memoryFrame))
    | apply aqT_seq
    | apply aqT_ite
    | refine aqT_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpItem_lookup (by simp) (rlpItem_acallee hw) ?_ ?_

def AHp (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ hp : BitVec 64, L.lookup (ofString "p") = some (.val (.word hp)) ∧ P0.toNat ≤ hp.toNat ∧ hp.toNat ≤ 33806089496

def AHn (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ hp n : BitVec 64, L.lookup (ofString "p") = some (.val (.word hp)) ∧ P0.toNat ≤ hp.toNat ∧
    hp.toNat ≤ 33806089496 ∧ L.lookup (ofString "n") = some (.val (.word n)) ∧ n ≤ (33806089496 : BitVec 64) - hp

def AHq (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ q : BitVec 64, L.lookup (ofString "q") = some (.val (.word q)) ∧ P0.toNat ≤ q.toNat

def AHq2 (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ q : BitVec 64, L.lookup (ofString "q") = some (.val (.word q)) ∧ P0.toNat ≤ q.toNat ∧ q.toNat ≤ 33806089496

/-- `alloc` keeps every word of memory in every outcome, and every continuing outcome leaves the heap pointer in
`[P0, HEAP_END]` with the frame and scratch pointers untouched. -/
theorem alloc_aq :
    AQ SP0 P0 FM w (fun _ => True) (fun _ => True) (fun _ => True) (sourceFunctionBody Guest.guestFn_alloc) := by
  rw [source_alloc_body]
  unfold allocationAfterPointer allocationFinish
  refine aq_dec (Pb := AHp P0) (Qb := fun _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s v aw _ _ ev _
    obtain ⟨_,_,⟨hp,hhp,lo,hi⟩⟩ := aw
    simp [EV,evalHOLExact,hhp] at ev
    subst ev
    exact ⟨hp,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi⟩
  refine aq_seq (Q := AHn P0) (aq_ite (CT := fun _ => True) (CF := AHn P0) _ ?_ (aq_trapCall 1)
    (aq_conseq aq_skip (fun _ h => h) (fun _ h => h.2))) ?_
  · intro F s x _ ⟨hp,hhp,lo,hi⟩ sl ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    cases hn : s.locals.lookup (ofString "n") with
    | none =>
      simp [EV,allocationRequestCheck,evalHOLExact,evalListHOLExact,hhp,hn,wordOpHOL,wordOp,valueIsWord,
        valueWord] at ev
    | some nv =>
      obtain ⟨n,rfl⟩ := sl _ trivial nv hn
      refine ⟨hp,n,hhp,lo,hi,hn,?_⟩
      simp [EV,allocationRequestCheck,evalHOLExact,evalListHOLExact,hhp,hn,wordOpHOL,wordOp,valueIsWord,
        valueWord,Compiler.Encoders.Asm.wordCmpHOL] at ev
      exact BitVec.le_def.mpr (by omega)
  refine aq_dec (Pb := AHq P0) (Qb := fun _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s v _ ⟨hp,n,hhp,lo,hi,hn,req⟩ _ ev _
    simp only [EV] at ev
    rw [eval_allocationEndExpression s hp n hhp hn] at ev
    cases ev
    have sum := allocationGuard_sum_bound hp n hi req
    have cov := allocationEnd_covers hp n sum
    exact ⟨allocationEnd hp n,by simp [HolFiniteMapExact.lookup_update,FUPDATE],by omega⟩
  refine aq_seq (Q := AHq2 P0) (aq_ite (CT := fun _ => True) (CF := AHq2 P0) _ ?_ (aq_trapCall 1)
    (aq_conseq aq_skip (fun _ h => h) (fun _ h => h.2))) (aq_seq (aq_assignHeap _ ?_) (aq_return _))
  · intro F s x _ ⟨q,hq,lo⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    simp [EV,evalHOLExact,hq,Compiler.Encoders.Asm.wordCmpHOL] at ev
    have := BitVec.le_def.mp ev
    exact ⟨q,hq,lo,by simpa using this⟩
  · intro F s v _ ⟨q,hq,lo,hi⟩ _ ev
    simp [EV,evalHOLExact,hq] at ev
    subst ev
    exact ⟨q,rfl,lo,hi⟩

theorem alloc_acallee : ACallee SP0 P0 FM w (sourceFunctionBody Guest.guestFn_alloc) :=
  acallee_of_aq alloc_aq

#print axioms alloc_acallee
#print axioms rlpItemTotal_acallee
#print axioms rlpListCount_acallee
#print axioms rlpItem_acallee
#print axioms rlpDecodeFully_acallee
end InitECandidate.Runtime
