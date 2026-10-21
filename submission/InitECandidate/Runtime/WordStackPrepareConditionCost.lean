import InitECandidate.Runtime.WordStackConditionCost
import InitECandidate.Runtime.WordStackInstructionCost
import InitECandidate.Runtime.InstBudget
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.If
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

private theorem loadConditionCost {F : Type} (loads : List (Nat × Nat))
    (target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (comparison : Cmp) (register : Nat) (operand : HolRegImm 64)
    (first second : HolProg 64) (x y : WordLocW 64) (value : Bool)
    (small : ∀ entry ∈ loads, entry.2 ≤ 91)
    (run : StackSemEvaluate.evaluate (wStackLoadNative loads .skip, target) = (none, post))
    (left : StackSemStateOps.getVar register post = some x)
    (right : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) post = some y)
    (compared : wordSemWordCmp comparison x y = some value) (clock : Nat) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative loads (.ite comparison register operand first second)) {target with clock := clock} ≤
      7 * loads.length + 11 + stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (if value then first else second) {post with clock := clock} := by
  have runClock : StackSemEvaluate.evaluate (wStackLoadNative loads .skip, {target with clock := clock}) =
      (none, {post with clock := clock}) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run]
    rfl
  have leftClock : StackSemStateOps.getVar register {post with clock := clock} = some x := left
  have rightClock : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
      {post with clock := clock} = some y := by
    cases operand <;> simpa [HolRegImm.toWordRegImm, StackSemStateOps.getVarImm, StackSemStateOps.getVar] using right
  exact wordStackLoad_condition_cost loads comparison register operand first second _ _ x y value
    small runClock leftClock rightClock compared

/-- Full original condition preparation, strengthened with an executed-cost
routing bound. Spills, rejected immediates, and the exact loaded state are
proved from the original relation and source operands. -/
theorem prepareCondition_cost {F : Type}
    (ac : AsmConfigExact 64) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec 64)) (k f frame : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (x y : WordLocW 64) (value : Bool)
    (related : stateRel ac k f frame source target lens 0)
    (leftEven : register % 2 = 0)
    (rightEven : OperandEven operand)
    (left : WordSemStateFiniteExact.getVar register source = some x)
    (right : WordSemStateFiniteExact.getVarImm operand source = some y)
    (compared : wordSemWordCmp comparison x y = some value)
    (small : f ≤ 92) :
    ∃ post : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stateRel ac k f frame source post lens 0 ∧ target.clock = post.clock ∧
      target.bitmaps.IsPrefix post.bitmaps ∧ sptSubspt target.code post.code ∧
      (∀ (first second : HolProg 64) (clock : Nat),
        StackSemEvaluate.evaluate
          (conditionProgram ac comparison register operand (k,f,frame) first second,
            {target with clock := clock}) =
        StackSemEvaluate.evaluate (if value then first else second, {post with clock := clock})) ∧
      ∀ (first second : HolProg 64) (clock : Nat),
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (conditionProgram ac comparison register operand (k,f,frame) first second)
          {target with clock := clock} ≤
          30 + stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
            (if value then first else second) {post with clock := clock} := by
  rcases regCompile : wReg1 register (k,f,frame) with ⟨loads, physical⟩
  have loadFacts := wordReg1_loads register (k,f,frame) small
  rw [regCompile] at loadFacts
  dsimp only at loadFacts
  cases operand with
  | reg other =>
    obtain ⟨middle, loadRun, firstClock, firstRel, _, _, _, _, physicalNe, firstRead⟩ :=
      LoadRegister.evaluateWStackLoadWReg1 ac k f frame register physical loads
        source target lens x regCompile leftEven left related
    rcases otherCompile : wReg2 other (k,f,frame) with ⟨otherLoads, otherPhysical⟩
    obtain ⟨post, otherRun, secondClock, _, secondRel, _, _, preserve, _, secondRead⟩ :=
      LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame other otherPhysical otherLoads
        source middle lens y otherCompile rightEven right firstRel
    have bothRun : StackSemEvaluate.evaluate (wStackLoadNative (loads ++ otherLoads) .skip,target) =
        (none,post) := by
      rw [wStackLoadAppend, Function.comp_apply, LoadRegister.evaluateWStackLoadSeq,
        StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, loadRun]
      exact otherRun
    have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
      (wStackLoadNative (loads ++ otherLoads) .skip) target post none bothRun
    refine ⟨post, secondRel, firstClock.trans secondClock, mono.1, mono.2, ?_, ?_⟩
    · intro first second clock
      simp only [conditionProgram, regCompile, otherCompile]
      exact loadConditionRun (loads ++ otherLoads) target post comparison physical (.reg otherPhysical) first second x y value bothRun
        ((preserve physical physicalNe).trans firstRead) secondRead compared clock
    · intro first second clock
      simp only [conditionProgram, regCompile, otherCompile]
      have otherFacts := wordReg2_loads other (k,f,frame) small
      rw [otherCompile] at otherFacts
      dsimp only at otherFacts
      have bothSmall : ∀ entry ∈ loads ++ otherLoads, entry.2 ≤ 91 := by
        intro entry member
        rcases List.mem_append.mp member with member | member
        · exact loadFacts.2 entry member
        · exact otherFacts.2 entry member
      have cost := loadConditionCost (loads ++ otherLoads) target post comparison physical
        (.reg otherPhysical) first second x y value bothSmall bothRun
        ((preserve physical physicalNe).trans firstRead) secondRead compared clock
      simp only [List.length_append] at cost
      omega
  | imm word =>
    simp only [WordSemStateFiniteExact.getVarImm, Option.some.injEq] at right
    subst y
    by_cases immediate : ac.validImm (.inr comparison) word = true
    · obtain ⟨post, loadRun, sameClock, postRel, _, _, _, _, _, firstRead⟩ :=
        LoadRegister.evaluateWStackLoadWReg1 ac k f frame register physical loads
          source target lens x regCompile leftEven left related
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        (wStackLoadNative loads .skip) target post none loadRun
      refine ⟨post, postRel, sameClock, mono.1, mono.2, ?_, ?_⟩
      · intro first second clock
        simp only [conditionProgram, regCompile, immediate, if_true]
        exact loadConditionRun loads target post comparison physical (.imm word) first second x (.word word) value loadRun firstRead rfl compared clock
      · intro first second clock
        simp only [conditionProgram, regCompile, immediate, if_true]
        have cost := loadConditionCost loads target post comparison physical (.imm word)
          first second x (.word word) value loadFacts.2 loadRun firstRead rfl compared clock
        omega
    · obtain ⟨constantPost, constantRun, constantClock, constantRel, _, _, constantRead⟩ :=
        ConstantInstruction.evaluateConstInst ac k f frame 0 source target lens word related
      obtain ⟨post, loadRun, sameClock, postRel, _, _, _, preserve, _, firstRead⟩ :=
        LoadRegister.evaluateWStackLoadWReg1 ac k f frame register physical loads
          source constantPost lens x regCompile leftEven left constantRel
      have secondRead : StackSemStateOps.getVar (k+1) post = some (.word word) :=
        (preserve (k+1) (by omega)).trans constantRead
      have prefixRun : StackSemEvaluate.evaluate
          (.seq (.inst (.const (k+1) word)) (wStackLoadNative loads .skip),target) = (none,post) := by
        rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, constantRun]
        exact loadRun
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        (.seq (.inst (.const (k+1) word)) (wStackLoadNative loads .skip)) target post none prefixRun
      refine ⟨post, postRel, constantClock.trans sameClock, mono.1, mono.2, ?_, ?_⟩
      · intro first second clock
        simp only [conditionProgram, regCompile, immediate, Bool.false_eq_true, if_false]
        rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
          ConstantInstruction.evaluateConstInstClock, constantRun]
        simp only [Prod.map, id_eq]
        exact loadConditionRun loads constantPost post comparison physical (.reg (k+1)) first second x (.word word) value loadRun firstRead secondRead compared clock

      · intro first second clock
        simp only [conditionProgram, regCompile, immediate, Bool.false_eq_true, if_false]
        have constRunClock : StackSemEvaluate.evaluate
            (.inst (.const (k+1) word), {target with clock := clock}) =
              (none, {constantPost with clock := clock}) := by
          rw [ConstantInstruction.evaluateConstInstClock, constantRun]
          rfl
        rw [stackExecutionCost_seq]
        simp only [show removalLocalPrice 6 riscvConfig.addrOffset
            (.seq (.inst (.const (k+1) word))
              (wStackLoadNative loads (.ite comparison physical (.reg (k+1)) first second))) = 0 from rfl,
          Nat.zero_add, constRunClock]
        have cost := loadConditionCost loads constantPost post comparison physical (.reg (k+1))
          first second x (.word word) value loadFacts.2 loadRun firstRead secondRead compared clock
        have constCost : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
            (.inst (.const (k+1) word)) {target with clock := clock} ≤ 12 := by
          have bound := const_native_length_le (k+1) word
          simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
            using Nat.add_le_add_right bound 6
        omega

#print axioms prepareCondition_cost
end InitECandidate.Runtime.StackToLab
