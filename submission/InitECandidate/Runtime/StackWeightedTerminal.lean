import InitECandidate.Runtime.StackWeightedCompose
import InitECandidate.Runtime.LabTerminal
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- A compiled terminating fragment supplies its actual weighted prefix and
terminal instruction. The terminal's native overhead is charged once by the
native extraction theorem, separately from recursive prefix prices. -/
def TerminalWeightedFlatten {F : Type} (program : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (price : LabProgHOL 64 → Nat → Nat) : Prop :=
  ∀ (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64),
    FlattenHyps program source flag (some result) post sectionId labelId continues breaks start →
    ∃ final steps work, final.ffi = post.ffi ∧ final.code = start.code ∧
      work ≤ price encoded start.pc ∧
      LabToTarget.WeightedInstructionTrace encoded {start with clock := start.clock + steps} final work ∧
      LabToTarget.Terminal final outcome

private theorem terminal_appList {α : Type} (lines : List α) :
    appListAppend (.list lines) = lines := (appListAppend_thm .nil .nil lines).2.1

/-- Actual flattened Halt, including its success/resource-limit distinction.
The operand comes from the source register and the original ABI relation. -/
theorem terminalWeightedFlatten_halt {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (reg : Nat) (value : BitVec 64)
    (read : StackSemStateOps.getVar reg source = some (.word value)) :
    TerminalWeightedFlatten (.halt reg) source (.halt (.word value))
      (if value = 0 then .success else .resourceLimitHit) (fun _ _ => 0) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, args, installed, _⟩
  rw [StackSemEvaluate.evaluate_halt, read] at evaluated
  simp only [Prod.mk.injEq] at evaluated
  obtain ⟨_, rfl⟩ := evaluated
  have fetch : asmFetchAux start.pc start.code = some (.labAsm .halt 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, terminal_appList] using installed)
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  have operand : start.regs start.ptrReg = .word value := by
    rw [← args]; exact InstCorrect.regOfLookup related read
  let final := {start with clock := start.clock + 1}
  refine ⟨final, 1, 0, ?_, rfl, Nat.le_refl _, LabToTarget.WeightedInstructionTrace.nil _, ?_⟩
  · simpa only [final, StackSemStateOps.emptyEnv] using relFfi related
  · exact LabToTarget.Terminal.halt final 0 value [] 0 (by simp [final])
      (by simpa only [final, asmFetch] using fetch) operand

/-- The composed prefix and terminal instruction yield the actual native halt
and final FFI state. The fixed terminal ceiling appears once, after the entire
prefix, rather than once per recursive block. -/
theorem TerminalWeightedFlatten.native {F : Type}
    {program : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {result : StackSemResult 64} {outcome : HolOutcome} {price : LabProgHOL 64 → Nat → Nat}
    (compiledBound : TerminalWeightedFlatten program source result outcome price)
    (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps program source flag (some result) post sectionId labelId continues breaks start)
    (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (target : mc.target = Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base) start asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine start) :
    ∃ count native, count ≤ price encoded start.pc + 17 ∧
      evaluateTargetHOL mc start.ffi count machine = (.halt outcome, native, post.ffi) := by
  obtain ⟨final, steps, work, ffi, _, bound, trace, terminal⟩ :=
    compiledBound flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨prefixCount, middle, middleAsm, prefixBound, prefixRun, middleRelated, _⟩ :=
    LabToTarget.weightedInstructionTrace_with_oracle encoded trace mc labs base asm machine target encoder
      (Flapjack.Compiler.Backend.LabToTarget.stateRelClock _ start asm machine (start.clock + steps) related)
      (Flapjack.Compiler.Backend.LabToTarget.oracleTie_clock mc machine start (start.clock + steps) tie)
  obtain ⟨lastCount, native, lastBound, lastRun⟩ := LabToTarget.terminal_native terminal
    (Compiler.Backend.Semantics.TargetProps.shiftInterfer prefixCount mc) encoded labs base middleAsm middle
    target encoder middleRelated
  refine ⟨prefixCount + lastCount, native, by omega, ?_⟩
  rw [Nat.add_comm prefixCount lastCount, prefixRun lastCount, lastRun, ffi]

/-- An actual early terminal first child leaves its suffix unexecuted. -/
theorem terminalWeightedFlatten_seq_stop {F : Type}
    (first second : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome) (price : LabProgHOL 64 → Nat → Nat)
    (exits : ∃ post, StackSemEvaluate.evaluate (first, source) = (some result, post))
    (bound : TerminalWeightedFlatten first source result outcome price) :
    TerminalWeightedFlatten (.seq first second) source result outcome price := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  obtain ⟨middle, firstRun⟩ := exits
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, firstRun] at evaluated
  have postEq : middle = post := (Prod.mk.inj evaluated).2
  subst post
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at args
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false first sectionId labelId continues breaks with ⟨xs, nr1, l1⟩
  rcases h2 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false second sectionId l1 continues breaks with ⟨ys, nr2, l2⟩
  have flat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL flag
      (.seq first second) sectionId labelId continues breaks).1 =
      appListAppend xs ++ ((if flag then [.label sectionId 1 0] else []) ++ appListAppend ys) := by
    rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    cases flag <;> simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [flat] at installed
  have installedFirst := (codeInstalledAppendImp _ _ _ _ installed).1
  exact bound false middle sectionId labelId continues breaks start encoded
    ⟨firstRun, nonerror, related, args.1, by rw [h1]; exact installedFirst, labels⟩

/-- A normal prefix composes with its reached terminal suffix. No additional
terminal surcharge is inserted by this recursive sequence rule. -/
theorem terminalWeightedFlatten_seq_next {F : Type}
    (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (exit : StackSemResult 64) (outcome : HolOutcome)
    (firstNormal : (StackSemEvaluate.evaluate (first, source)).1 = none)
    (firstPrice secondPrice : LabProgHOL 64 → Nat → Nat)
    (firstBound : NormalWeightedFlatten first source firstPrice)
    (secondBound : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      TerminalWeightedFlatten second middle exit outcome secondPrice)
    (price : LabProgHOL 64 → Nat → Nat)
    (envelope : ∀ encoded pc sectionId labelId continues breaks,
      firstPrice encoded pc + secondPrice encoded (pc + ((appListAppend
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL false first sectionId labelId continues breaks).1).filter
          (fun line => !isLabelHOL line)).length) ≤ price encoded pc) :
    TerminalWeightedFlatten (.seq first second) source exit outcome price := by
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
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨prefixResult, middle⟩
  rw [firstRun] at evaluated
  cases prefixResult with
  | some value => rw [firstRun] at firstNormal; contradiction
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
    obtain ⟨final, steps2, work2, ffi, code2, bound2, trace2, terminal⟩ :=
      secondBound middle firstRun false post sectionId l1 continues breaks mid encoded
        ⟨evaluated, nonerror, related1, argsMid, by rw [h2]; exact installedMid, labelsMid⟩
    refine ⟨final, steps1 + steps2, work1 + work2, ffi, code2.trans code1, ?_, ?_, terminal⟩
    · have budget := envelope encoded start.pc sectionId labelId continues breaks
      rw [h1] at budget
      rw [pc1] at bound2
      omega
    · have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) trace2
      simpa only [Nat.add_assoc] using joined



#print axioms terminalWeightedFlatten_seq_stop
#print axioms terminalWeightedFlatten_seq_next
#print axioms terminalWeightedFlatten_halt
#print axioms TerminalWeightedFlatten.native
end InitECandidate.Runtime.StackToLab
