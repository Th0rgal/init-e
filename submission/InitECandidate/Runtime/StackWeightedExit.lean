import InitECandidate.Runtime.StackWeightedCompose
import InitECandidate.Runtime.StackWeightedControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

private theorem exit_appList {α : Type} (lines : List α) :
    appListAppend (.list lines) = lines := (appListAppend_thm .nil .nil lines).2.1

/-- A returned control location has been reached; Continue instead leaves the
loop's back jump pending, as in the original flattening result relation. -/
def WeightedExitDestination {F : Type} (result : StackSemResult 64)
    (sectionId : Nat) (continues breaks : List Nat)
    (final : LabSem.State 64 LabToTarget.Config F) : Prop :=
  match resultView result sectionId continues breaks with
  | .vloc sectionValue labelValue => locToPc sectionValue labelValue final.code = some final.pc
  | .vcont sectionValue labelValue => codeInstalled final.pc
      [.labAsm (.jump (.lab sectionValue labelValue)) 0 [] 0] final.code
  | _ => False

/-- Recursive weighted compiler motive for nonhalting control exits. Timeout,
error and FFI/halt outcomes require their own mixed/terminal trace rules. -/
def ExitWeightedFlatten {F : Type} (program : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (price : LabProgHOL 64 → Nat → Nat) : Prop :=
  ∀ (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64),
    FlattenHyps program source flag (some result) post sectionId labelId continues breaks start →
    ∃ final steps work, stateRel post final ∧ final.code = start.code ∧
      WeightedExitDestination result sectionId continues breaks final ∧ work ≤ price encoded start.pc ∧
      LabToTarget.WeightedInstructionTrace encoded {start with clock := start.clock + steps} final work

/-- A break executes its direct jump, with the destination justified by the
original installed-label premises and a two-instruction native allowance. -/
theorem exitWeightedFlatten_break {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (index : Nat) :
    ExitWeightedFlatten (.break index) source (.break index) (fun _ _ => 2) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨_, pc, destination, related, trace⟩ := flatten_break_weighted source index flag
    (some (.break index)) post sectionId labelId continues breaks start encoded hyps
  exact ⟨LabSem.updPc pc start, 1, 2, related, rfl, destination, Nat.le_refl _, trace⟩

/-- Continue itself costs zero native instructions: the original compiler
leaves its back jump pending for the loop rule, avoiding double charging. -/
theorem exitWeightedFlatten_continue {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (index : Nat) :
    ExitWeightedFlatten (.continue index) source (.continue index) (fun _ _ => 0) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_continue] at evaluated
  simp only [Prod.mk.injEq] at evaluated
  obtain ⟨_, rfl⟩ := evaluated
  refine ⟨start, 0, 0, related, rfl, ?_, Nat.le_refl _, ?_⟩
  · simpa [WeightedExitDestination, resultView,
      Flapjack.Compiler.Backend.StackToLab.flattenHOL,
      exit_appList] using installed
  · simpa only [Nat.add_zero] using LabToTarget.WeightedInstructionTrace.nil (code := encoded) start

/-- Return performs one indirect jump to a valid installed source-code
location. Validity is an explicit semantic protocol premise, not a cost bound. -/
theorem exitWeightedFlatten_return {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (reg sectionValue labelValue : Nat)
    (value : StackSemStateOps.getVar reg source = some (.loc sectionValue labelValue))
    (valid : StackSem.locCheckExact source.code (sectionValue, labelValue)) :
    ExitWeightedFlatten (.ret reg) source (.result (.loc sectionValue labelValue)) (fun _ _ => 1) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨pc, destination⟩ := StateRel.locCheckImpLocToPc ⟨valid, hyps.2.2.1⟩
  obtain ⟨_, related, trace⟩ := flatten_return_weighted source reg sectionValue labelValue pc flag
    (some (.result (.loc sectionValue labelValue))) post sectionId labelId continues breaks start encoded
    hyps value destination
  exact ⟨LabSem.updPc pc start, 1, 1, related, rfl, destination, Nat.le_refl _, trace⟩

/-- The exception return uses the same one-instruction indirect-jump
protocol as an ordinary return, at an installed handler location. -/
theorem exitWeightedFlatten_raise {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (reg sectionValue labelValue : Nat)
    (value : StackSemStateOps.getVar reg source = some (.loc sectionValue labelValue))
    (valid : StackSem.locCheckExact source.code (sectionValue, labelValue)) :
    ExitWeightedFlatten (.raise reg) source (.exception (.loc sectionValue labelValue)) (fun _ _ => 1) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_raise, value] at evaluated
  simp only [Prod.mk.injEq] at evaluated
  obtain ⟨_, rfl⟩ := evaluated
  obtain ⟨pc, destination⟩ := StateRel.locCheckImpLocToPc ⟨valid, related⟩
  have fetch : asmFetchAux start.pc start.code = some (.asm (.asmi (.jumpReg reg)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, exit_appList] using installed)
  exact ⟨LabSem.updPc pc start, 1, 1, related, rfl, destination, Nat.le_refl _,
    jumpreg_update_weighted start encoded reg sectionValue labelValue pc fetch
      (InstCorrect.regOfLookup related value) destination⟩

/-- An early control exit executes only the first child of Seq. The untouched
suffix contributes neither weighted work nor a native join instruction. -/
theorem exitWeightedFlatten_seq_stop {F : Type}
    (first second : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (price : LabProgHOL 64 → Nat → Nat)
    (exits : ∃ post, StackSemEvaluate.evaluate (first, source) = (some result, post))
    (bound : ExitWeightedFlatten first source result price) :
    ExitWeightedFlatten (.seq first second) source result price := by
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

/-- A normally returning prefix followed by a control exit composes the two
actual traces, with the original exit destination and no Seq overhead. -/
theorem exitWeightedFlatten_seq_next {F : Type}
    (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (exit : StackSemResult 64)
    (firstNormal : (StackSemEvaluate.evaluate (first, source)).1 = none)
    (firstPrice secondPrice : LabProgHOL 64 → Nat → Nat)
    (firstBound : NormalWeightedFlatten first source firstPrice)
    (secondBound : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      ExitWeightedFlatten second middle exit secondPrice)
    (price : LabProgHOL 64 → Nat → Nat)
    (envelope : ∀ encoded pc sectionId labelId continues breaks,
      firstPrice encoded pc + secondPrice encoded (pc + ((appListAppend
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL false first sectionId labelId continues breaks).1).filter
          (fun line => !isLabelHOL line)).length) ≤ price encoded pc) :
    ExitWeightedFlatten (.seq first second) source exit price := by
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
    obtain ⟨final, steps2, work2, related2, code2, destination, bound2, trace2⟩ :=
      secondBound middle firstRun false post sectionId l1 continues breaks mid encoded
        ⟨evaluated, nonerror, related1, argsMid, by rw [h2]; exact installedMid, labelsMid⟩
    refine ⟨final, steps1 + steps2, work1 + work2, related2, code2.trans code1, destination, ?_, ?_⟩
    · have budget := envelope encoded start.pc sectionId labelId continues breaks
      rw [h1] at budget
      rw [pc1] at bound2
      omega
    · have joined := LabToTarget.weightedInstructionTrace_append (trace1.add_clock steps2) trace2
      simpa only [Nat.add_assoc] using joined


/-- Composed control-exit prefixes execute on RISC-V with the certified local
price ceiling, actual destination, related state and advanced oracle tie. -/
theorem ExitWeightedFlatten.native {F : Type}
    {program : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {exit : StackSemResult 64} {price : LabProgHOL 64 → Nat → Nat}
    (compiledBound : ExitWeightedFlatten program source exit price)
    (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps program source flag (some exit) post sectionId labelId continues breaks start)
    (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64)
    (asm : Flapjack.AsmState 64) (machine : RiscV.L3.riscv_state)
    (target : mc.target = Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base) start asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine start) :
    ∃ final count native finalAsm, stateRel post final ∧ final.code = start.code ∧
      WeightedExitDestination exit sectionId continues breaks final ∧ count ≤ price encoded start.pc ∧
      (∀ clock, Flapjack.evaluateTargetHOL mc start.ffi (clock + count) machine =
        Flapjack.evaluateTargetHOL
          (Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc) final.ffi clock native) ∧
      Flapjack.Compiler.Backend.LabToTarget.stateRel
        (Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc, encoded, labs, base) final finalAsm native ∧
      Flapjack.Compiler.Backend.LabToTarget.oracleTie
        (Compiler.Backend.Semantics.TargetProps.shiftInterfer count mc) native final := by
  obtain ⟨final, steps, work, stackRelated, code, destination, bound, trace⟩ :=
    compiledBound flag post sectionId labelId continues breaks start encoded hyps
  obtain ⟨count, native, finalAsm, nativeBound, run, nativeRelated, finalTie⟩ :=
    LabToTarget.weightedInstructionTrace_with_oracle encoded trace mc labs base asm machine
      target encoder
      (Flapjack.Compiler.Backend.LabToTarget.stateRelClock _ start asm machine (start.clock + steps) related)
      (Flapjack.Compiler.Backend.LabToTarget.oracleTie_clock mc machine start (start.clock + steps) tie)
  exact ⟨final, count, native, finalAsm, stackRelated, code, destination, nativeBound.trans bound,
    run, nativeRelated, finalTie⟩


#print axioms ExitWeightedFlatten.native
#print axioms exitWeightedFlatten_raise
#print axioms exitWeightedFlatten_seq_next
#print axioms exitWeightedFlatten_seq_stop
#print axioms exitWeightedFlatten_return
#print axioms exitWeightedFlatten_continue
#print axioms exitWeightedFlatten_break
end InitECandidate.Runtime.StackToLab
