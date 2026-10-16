import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Leaves

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

def BoundedFlattenConcl {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) (budget : Nat := 1) : Prop :=
  ∃ (ck : Nat), ck ≤ budget ∧ ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
    match haltView r with
    | some res => evaluate { t1 with clock := t1.clock + ck } = (res, t2) ∧ t2.ffi = s2.ffi
    | none =>
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      match r.map (fun w => resultView w n cs bs) with
      | none =>
        t2.pc = t1.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t prog n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2
      | some (.vloc n1 n2) =>
        (∀ k, (sptLookup k s2.code).isSome → (locToPc k 0 t2.code).isSome) ∧
          ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2
      | some (.vcont n1 n2) =>
        stateRel s2 t2 ∧ codeInstalled t2.pc [.labAsm (.jump (.lab n1 n2)) 0 [] 0] t2.code
      | some .vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
      | some .verr => False

/-- `flatten_correct` for one program and initial state. -/
def BoundedFlattenProp {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) (budget : Nat := 1) : Prop :=
  ∀ (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
    FlattenHyps prog s1 t r s2 n l cs bs t1 → BoundedFlattenConcl prog t r s2 n l cs bs t1 budget


private theorem appList' {α : Type} (l : List α) : appListAppend (.list l) = l :=
  (appListAppend_thm .nil .nil l).2.1

section
variable {width : Nat} [NeZero width] {C F : Type}
/-- `Halt` case. -/
theorem flattenHalt_bounded (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    BoundedFlattenProp (.halt v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_halt] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm .halt 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at ca
  split at ev
  · rename_i w hw
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have hreg : t1.regs t1.ptrReg = w := by
      rw [← ca]; exact InstCorrect.regOfLookup rel hw
    refine ⟨1, by decide, { t1 with clock := t1.clock + 1 }, ?_, ?_⟩
    · rw [evaluate]
      simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch, hreg]
      cases w with
      | word value =>
        by_cases hv : value = 0#width
        · simp [haltWordView, hv]
        · simp [haltWordView, hv]
      | loc a b => simp [haltWordView]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Inst` case. -/
theorem flattenInst_bounded (s1 : StackSemStateFiniteExact width C F) (i : HolInst width) :
    BoundedFlattenProp (.inst i : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_inst] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst i)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split at ev
  · rename_i s1' hi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have rel2 := InstCorrect.instCorrect ⟨hi, rel⟩
    obtain ⟨cpc, ccode, cclock, -, -, -, -, -, cptr, clen, cptr2, clen2, clink⟩ :=
      asmInstConsts i t1
    have nf := InstCorrect.notFailed rel2
    refine ⟨1, by decide, incPc (asmInst i t1), fun ck1 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rel2⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
        Flapjack.Compiler.Backend.LabProps.asmInstWithClock, nf, Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock, cclock, cpc]
      congr 1 <;> first | omega | exact nf.symm
    all_goals simp [incPc, cptr, clen, cptr2, clen2, clink, ccode, cpc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList',
      isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr


/-- Every installed StackSem procedure has a LabSem entry position. -/
private theorem boundedCodeLookupLocToPc {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    ∀ k, (sptLookup k s.code).isSome → (locToPc k 0 t.code).isSome := by
  intro k hk
  obtain ⟨prog, hp⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨-, pc, -, entry⟩ := rel.2.2.2.2.2.2.2.2.1 k prog hp
  simp [entry]

/-- `Tick` case. -/
theorem flattenTick_bounded (s1 : StackSemStateFiniteExact width C F) :
    BoundedFlattenProp (.tick : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_tick] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst .skip)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  have nf := InstCorrect.notFailed rel
  have clk := relClock rel
  split_ifs at ev with h0
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨1, by decide, incPc t1, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, StackSemStateOps.emptyEnv, relFfi rel]
    · simp [incPc]; omega
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, by decide, incPc (decClock t1), fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      ?_, StateRel.stateRelDecClock rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 0 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, decClock, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList', isLabelHOL]

/-- Shared step of `Return` and `Raise`: a register jump to a `Loc`. -/
theorem jumpRegLoc_bounded {s : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {reg l1 l2 : Nat}
    (rel : stateRel s t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg reg)) [] 0))
    (hreg : t1.regs reg = .loc l1 l2) :
    ∃ (ck : Nat), ck ≤ 1 ∧ ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      (∀ k, (sptLookup k s.code).isSome → (locToPc k 0 t2.code).isSome) ∧
      ∀ w, locToPc l1 l2 t2.code = some w → w = t2.pc ∧ stateRel s t2 := by
  cases hpc : locToPc l1 l2 t1.code with
  | none =>
    refine ⟨1, by decide, { t1 with clock := t1.clock + 1 }, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, fun k hk => boundedCodeLookupLocToPc rel k hk, ?_⟩
    · simp only [Nat.add_assoc]
    · intro w hw; simp [hpc] at hw
  | some pc =>
    refine ⟨1, by decide, updPc pc t1, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      boundedCodeLookupLocToPc rel, fun w hw => ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, hreg, hpc]
      congr 1
      simp only [updPc, decClock]
      congr 1
      omega
    · simp only [updPc] at hw ⊢
      rw [hpc] at hw
      exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `Return` case. -/
theorem flattenRet_bounded (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    BoundedFlattenProp (.ret v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_ret] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    exact jumpRegLoc_bounded rel fetch (InstCorrect.regOfLookup rel hv)
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Raise` case. -/
theorem flattenRaise_bounded (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    BoundedFlattenProp (.raise v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_raise] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    exact jumpRegLoc_bounded rel fetch (InstCorrect.regOfLookup rel hv)
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Break` case. -/
theorem flattenBreak_bounded (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedFlattenProp (.break k : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, inst, labs⟩
  rw [StackSemEvaluate.evaluate_break] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jump (.lab n (Flapjack.Compiler.Backend.StackToLab.findLabHOL k bs))) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  have some_ : (locToPc n (Flapjack.Compiler.Backend.StackToLab.findLabHOL k bs) t1.code).isSome := by
    by_cases hm : Flapjack.Compiler.Backend.StackToLab.findLabHOL k bs ∈ bs
    · exact labs _ (by simp [hm])
    · rw [notMemFindLabImp bs k hm]; exact labs 0 (by simp)
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp some_
  refine ⟨1, by decide, updPc pc t1, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
    boundedCodeLookupLocToPc rel, fun w hw => ?_⟩
  · rw [evaluate]
    simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue, hpc]
    congr 1
    simp only [updPc, decClock]
    congr 1
    omega
  · simp only [updPc] at hw ⊢
    rw [hpc] at hw
    exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `LocValue` case. -/
theorem flattenLocValue_bounded (s1 : StackSemStateFiniteExact width C F) (reg l1 l2 : Nat) :
    BoundedFlattenProp (.locValue reg l1 l2 : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_locValue] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.locValue reg (.lab l1 l2)) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split_ifs at ev with check
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨pc, hpc⟩ := StateRel.locCheckImpLocToPc ⟨check, rel⟩
    refine ⟨1, by decide, incPc (updReg reg (.loc l1 l2) t1), fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, StateRel.setVarUpdReg rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue,
        hpc, reduceCtorEq]
      congr 1
      simp only [incPc, decClock, updReg, labToLoc]
      congr 1
      omega
    · simp [incPc, updReg, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList', isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

theorem boundedStateRelWithCodeBuffer {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    (cb : WordSemBuffer width 8) :
    stateRel { s with codeBuffer := cb } { t with codeBuffer := cb } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, _, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, rfl, h23, h24, h25, h26, h27, h28, h29⟩

/-- `CodeBufferWrite` case. -/
theorem flattenCodeBufferWrite_bounded (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) :
    BoundedFlattenProp (.codeBufferWrite r1 r2 : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_codeBufferWrite] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.cbw r1 r2) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  have cbEq : s1.codeBuffer = t1.codeBuffer := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split at ev
  · rename_i w1 w2 h1 h2
    split at ev
    · rename_i cb hcb
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨1, by decide, incPc { t1 with codeBuffer := cb }, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, boundedStateRelWithCodeBuffer rel cb⟩
      · rw [evaluate]
        simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
          InstCorrect.regOfLookup rel h1, InstCorrect.regOfLookup rel h2, ← cbEq, hcb]
        congr 1
        simp only [incPc, decClock]
        congr 1
        omega
      · simp [incPc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList', isLabelHOL]
    · simp only [Prod.mk.injEq] at ev
      exact absurd ev.1.symm nerr
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Continue` case. -/
theorem flattenContinue_bounded (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedFlattenProp (.continue k : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_continue] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  refine ⟨0, by decide, t1, fun ck1 => rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, rel, ?_⟩
  simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst


end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.flattenInst_bounded
#print axioms InitECandidate.Runtime.StackToLab.flattenHalt_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenTick_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenRet_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenRaise_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenBreak_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenLocValue_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenCodeBufferWrite_bounded

#print axioms InitECandidate.Runtime.StackToLab.flattenContinue_bounded
