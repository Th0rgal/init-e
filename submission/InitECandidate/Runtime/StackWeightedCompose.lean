import InitECandidate.Runtime.StackWeightedBlock
import Flapjack.Compiler.Backend.LabToTarget.StateTransport
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- The weighted instruction/control prefix preserves compiler ABI metadata.
These are register indices, not the values stored in those registers. -/
theorem weightedTrace_metadata {F : Type} {encoded : LabProgHOL 64}
    {start final : LabSem.State 64 LabToTarget.Config F} {work : Nat}
    (trace : LabToTarget.WeightedInstructionTrace encoded start final work) :
    final.code = start.code ∧ final.ptrReg = start.ptrReg ∧
      final.lenReg = start.lenReg ∧ final.ptr2Reg = start.ptr2Reg ∧
      final.len2Reg = start.len2Reg ∧ final.linkReg = start.linkReg := by
  induction trace with
  | step state final instruction bytes n length clock fetch success rest ih =>
    obtain ⟨_, code, _, _, _, _, _, _, ptr, len, ptr2, len2, link⟩ := asmInstConsts instruction state
    simpa only [incPc, decClock, code, ptr, len, ptr2, len2, link] using ih
  | _ => simp_all only [incPc, decClock, LabSem.updPc, LabSem.updReg, and_self]

/-- A normal, code-preserving compiled fragment supplies its own weighted
execution trace. Costs may depend on its installed position and actual encoding.
This motive is for recursive compiler proofs, not an assumed native bound. -/
def NormalWeightedFlatten {F : Type} (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (price : LabProgHOL 64 → Nat → Nat) : Prop :=
  ∀ (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64),
    FlattenHyps p source flag none post sectionId labelId continues breaks start →
    ∃ final steps work, stateRel post final ∧
      final.pc = start.pc + ((appListAppend
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag p sectionId labelId continues breaks).1).filter
          (fun line => !isLabelHOL line)).length ∧
      final.code = start.code ∧ work ≤ price encoded start.pc ∧
      LabToTarget.WeightedInstructionTrace encoded {start with clock := start.clock + steps} final work

/-- The motive is discharged for actual ordinary blocks by their existing
compiler proof, including instruction failures ruled out by original premises. -/
theorem normalWeightedFlatten_instructionBlock {F : Type}
    (instructions : List (HolInst 64))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    NormalWeightedFlatten (instructionBlock instructions) source
      (fun encoded pc => instructionBlockWork encoded pc instructions) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨final, related, pc, code, trace⟩ := flatten_instructionBlock_weighted
    instructions source post flag sectionId labelId continues breaks start encoded hyps
  have lines := (flatten_instructionBlock_lines instructions flag sectionId labelId continues breaks).2
  have lengthEq := congrArg List.length lines
  simp only [List.length_map] at lengthEq
  exact ⟨final, instructions.length, instructionBlockWork encoded start.pc instructions,
    related, by simpa only [lengthEq] using pc, code, Nat.le_refl _, trace⟩

/-- Sequencing adds the actual weighted subtraces. It adds neither a native
instruction for Seq nor a multiplier to either recursive child's price. Only
the second source state actually reached by the first fragment is required. -/
theorem normalWeightedFlatten_seq {F : Type}
    (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (firstPrice secondPrice : LabProgHOL 64 → Nat → Nat)
    (firstBound : NormalWeightedFlatten first source firstPrice)
    (secondBound : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      NormalWeightedFlatten second middle secondPrice)
    (price : LabProgHOL 64 → Nat → Nat)
    (envelope : ∀ encoded pc sectionId labelId continues breaks,
      firstPrice encoded pc + secondPrice encoded (pc + ((appListAppend
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL false first sectionId labelId continues breaks).1).filter
          (fun line => !isLabelHOL line)).length) ≤ price encoded pc) :
    NormalWeightedFlatten (.seq first second) source price := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at evaluated
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false first sectionId labelId continues breaks with ⟨xs, nr1, l1⟩
  rcases h2 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false second sectionId l1 continues breaks with ⟨ys, nr2, l2⟩
  have flat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.seq first second) sectionId labelId continues breaks).1 =
      appListAppend xs ++ ((if flag then [.label sectionId 1 0] else []) ++ appListAppend ys) := by
    rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    cases flag <;> simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [flat] at installed
  obtain ⟨installedFirst, installedRest⟩ := codeInstalledAppendImp _ _ _ _ installed
  have installedSecond : codeInstalled (start.pc + ((appListAppend xs).filter
      (fun line => !isLabelHOL line)).length) (appListAppend ys) start.code := by
    cases flag
    · simpa using installedRest
    · simp only [if_true, List.singleton_append, codeInstalled_cons, isLabelHOL] at installedRest
      exact installedRest.2
  have flatLength : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.seq first second) sectionId labelId continues breaks).1).filter
        (fun line => !isLabelHOL line)).length =
      ((appListAppend xs).filter (fun line => !isLabelHOL line)).length +
        ((appListAppend ys).filter (fun line => !isLabelHOL line)).length := by
    rw [flat]; cases flag <;> simp [List.filter_append, isLabelHOL]
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  rw [firstRun] at evaluated
  cases result with
  | some value => simp at evaluated
  | none =>
    obtain ⟨mid, steps1, work1, related1, pc1, code1, bound1, trace1⟩ :=
      firstBound false middle sectionId labelId continues breaks start encoded
        ⟨firstRun, by simp, related, args.1, by rw [h1]; exact installedFirst, labels⟩
    rw [h1] at pc1
    have installedMid : codeInstalled mid.pc (appListAppend ys) mid.code := by
      rw [pc1, code1]; exact installedSecond
    have metadata := weightedTrace_metadata trace1
    have argsMid : StackProps.callArgs second mid.ptrReg mid.lenReg mid.ptr2Reg mid.len2Reg mid.linkReg := by
      simpa only [metadata.2.1, metadata.2.2.1, metadata.2.2.2.1, metadata.2.2.2.2.1, metadata.2.2.2.2.2] using args.2
    have labelsMid : ∀ k ∈ continues ++ breaks ++ [0], (locToPc sectionId k mid.code).isSome := by
      simpa only [code1] using labels
    obtain ⟨final, steps2, work2, related2, pc2, code2, bound2, trace2⟩ :=
      secondBound middle firstRun false post sectionId l1 continues breaks mid encoded
        ⟨evaluated, by simp, related1, argsMid, by rw [h2]; exact installedMid, labelsMid⟩
    refine ⟨final, steps1 + steps2, work1 + work2, related2, ?_, code2.trans code1, ?_, ?_⟩
    · rw [flatLength, pc2, h2, pc1]
      simp only [Prod.fst, Nat.add_assoc]
    · have budget := envelope encoded start.pc sectionId labelId continues breaks
      rw [h1] at budget
      rw [pc1] at bound2
      omega
    · have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) trace2
      simpa only [Nat.add_assoc] using joined

/-- A normal fragment's composed weighted trace executes on the actual native
machine, preserving the oracle tie for the next fragment. The only cost ceiling
is the recursively proved fragment price. -/
theorem NormalWeightedFlatten.native {F : Type}
    {program : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {price : LabProgHOL 64 → Nat → Nat}
    (compiledBound : NormalWeightedFlatten program source price)
    (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps program source flag none post sectionId labelId continues breaks start)
    (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64)
    (asm : Flapjack.AsmState 64) (machine : RiscV.L3.riscv_state)
    (target : mc.target = Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base) start asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine start) :
    ∃ final count native finalAsm, stateRel post final ∧ final.code = start.code ∧
      count ≤ price encoded start.pc ∧
      (∀ clock, Flapjack.evaluateTargetHOL mc start.ffi (clock + count) machine =
        Flapjack.evaluateTargetHOL
          (Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc) final.ffi clock native) ∧
      Flapjack.Compiler.Backend.LabToTarget.stateRel
        (Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc, encoded, labs, base) final finalAsm native ∧
      Flapjack.Compiler.Backend.LabToTarget.oracleTie
        (Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc) native final := by
  obtain ⟨final, steps, work, stackRelated, _, code, bound, trace⟩ :=
    compiledBound flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨count, native, finalAsm, nativeBound, run, nativeRelated, finalTie⟩ :=
    LabToTarget.weightedInstructionTrace_with_oracle encoded trace mc labs base asm machine
      target encoder
      (Flapjack.Compiler.Backend.LabToTarget.stateRelClock _ start asm machine (start.clock + steps) related)
      (Flapjack.Compiler.Backend.LabToTarget.oracleTie_clock mc machine start (start.clock + steps) tie)
  exact ⟨final, count, native, finalAsm, stackRelated, code, nativeBound.trans bound,
    run, nativeRelated, finalTie⟩

#print axioms NormalWeightedFlatten.native
#print axioms normalWeightedFlatten_instructionBlock
#print axioms weightedTrace_metadata
#print axioms normalWeightedFlatten_seq
end InitECandidate.Runtime.StackToLab
