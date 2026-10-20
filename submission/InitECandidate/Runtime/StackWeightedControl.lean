import InitECandidate.Runtime.StackWeightedInstruction
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

private theorem control_appList {α : Type} (lines : List α) :
    appListAppend (.list lines) = lines := (appListAppend_thm .nil .nil lines).2.1

/-- One installed direct jump has a two-step native allowance independent of
ROM length or displacement. Clock lifting supplies the one label step only. -/
theorem jump_update_weighted {F : Type}
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64) (label : Lab) (pc : Nat)
    (fetch : asmFetchAux start.pc start.code = some (.labAsm (.jump label) 0 [] 0))
    (destination : getPcValue label start = some pc) :
    LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
      (updPc pc start) 2 := by
  have successor : updPc pc (decClock { start with clock := start.clock + 1 }) = updPc pc start := by
    simp only [decClock, updPc, Nat.add_sub_cancel]
  have step := LabToTarget.WeightedInstructionTrace.jump (code := encoded)
    { start with clock := start.clock + 1 } (updPc pc start) label pc 0 [] 0 0
    (by simp) (by simpa only [asmFetch] using fetch) destination
    (by rw [successor]; exact .nil _)
  simpa only [Nat.zero_add] using step

/-- An installed location materialization uses its own line expansion and
padding allowance; it does not charge unrelated code bytes. -/
theorem locvalue_update_weighted {F : Type}
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64) (reg : Nat) (label : Lab) (pc : Nat)
    (fetch : asmFetchAux start.pc start.code = some (.labAsm (.locValue reg label) 0 [] 0))
    (destination : getPcValue label start = some pc) :
    LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
      (incPc (updReg reg (labToLoc label) start))
      (LabToTarget.controlWork 2 encoded start.pc) := by
  have successor : incPc (decClock (updReg reg (labToLoc label)
      { start with clock := start.clock + 1 })) = incPc (updReg reg (labToLoc label) start) := by
    simp only [updReg, decClock, incPc, Nat.add_sub_cancel]
  have step := LabToTarget.WeightedInstructionTrace.locValue (code := encoded)
    { start with clock := start.clock + 1 } (incPc (updReg reg (labToLoc label) start))
    reg label pc 0 [] 0 0 (by simp) (by simpa only [asmFetch] using fetch) destination
    (by rw [successor]; exact .nil _)
  simpa only [Nat.zero_add] using step

/-- Actual flattened Break reaches the original installed exit label. Its
native allowance is two, not a program-size multiplier. -/
theorem flatten_break_weighted {F : Type}
    (source : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (k : Nat) (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.break k) source flag result post sectionId labelId continues breaks start) :
    result = some (.break k) ∧ ∃ pc,
      locToPc sectionId (Flapjack.Compiler.Backend.StackToLab.findLabHOL k breaks) start.code = some pc ∧
      stateRel post (updPc pc start) ∧
      LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
        (updPc pc start) 2 := by
  rcases hyps with ⟨evaluated, _, related, _, installed, labels⟩
  rw [StackSemEvaluate.evaluate_break] at evaluated
  simp only [Prod.mk.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  have fetch : asmFetchAux start.pc start.code = some
      (.labAsm (.jump (.lab sectionId (Flapjack.Compiler.Backend.StackToLab.findLabHOL k breaks))) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, control_appList] using installed)
  have existsPc : (locToPc sectionId (Flapjack.Compiler.Backend.StackToLab.findLabHOL k breaks) start.code).isSome := by
    by_cases member : Flapjack.Compiler.Backend.StackToLab.findLabHOL k breaks ∈ breaks
    · exact labels _ (by simp [member])
    · rw [notMemFindLabImp breaks k member]
      exact labels 0 (by simp)
  obtain ⟨pc, destination⟩ := Option.isSome_iff_exists.mp existsPc
  exact ⟨rfl, pc, destination, related,
    jump_update_weighted start encoded _ pc fetch destination⟩

/-- Actual flattened LocValue preserves the original state relation and
provides the costed prefix for subsequent control or call code. -/
theorem flatten_locvalue_weighted {F : Type}
    (source : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (reg sectionValue labelValue : Nat) (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.locValue reg sectionValue labelValue) source flag result post
      sectionId labelId continues breaks start) :
    result = none ∧ ∃ pc,
      locToPc sectionValue labelValue start.code = some pc ∧
      stateRel post (incPc (updReg reg (.loc sectionValue labelValue) start)) ∧
      LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
        (incPc (updReg reg (.loc sectionValue labelValue) start))
        (LabToTarget.controlWork 2 encoded start.pc) := by
  rcases hyps with ⟨evaluated, nonerror, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_locValue] at evaluated
  have fetch : asmFetchAux start.pc start.code = some
      (.labAsm (.locValue reg (.lab sectionValue labelValue)) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, control_appList] using installed)
  split_ifs at evaluated with valid
  · simp only [Prod.mk.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    obtain ⟨pc, destination⟩ := StateRel.locCheckImpLocToPc ⟨valid, related⟩
    refine ⟨rfl, pc, destination, StateRel.setVarUpdReg related, ?_⟩
    simpa only [labToLoc] using locvalue_update_weighted start encoded reg
      (.lab sectionValue labelValue) pc fetch destination
  · simp only [Prod.mk.injEq] at evaluated
    exact False.elim (nonerror evaluated.1.symm)

/-- An actual indirect jump costs one RISC-V instruction. The explicit
location premise is the real callee/return protocol, not a quantitative oracle. -/
theorem jumpreg_update_weighted {F : Type}
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64) (reg sectionValue labelValue pc : Nat)
    (fetch : asmFetchAux start.pc start.code = some (.asm (.asmi (.jumpReg reg)) [] 0))
    (register : start.regs reg = .loc sectionValue labelValue)
    (destination : locToPc sectionValue labelValue start.code = some pc) :
    LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
      (updPc pc start) 1 := by
  have successor : updPc pc (decClock { start with clock := start.clock + 1 }) = updPc pc start := by
    simp only [decClock, updPc, Nat.add_sub_cancel]
  have step := LabToTarget.WeightedInstructionTrace.jumpReg (code := encoded)
    { start with clock := start.clock + 1 } (updPc pc start) reg sectionValue labelValue pc [] 0 0
    (by simp) (by simpa only [asmFetch] using fetch) register destination
    (by rw [successor]; exact .nil _)
  simpa only [Nat.zero_add] using step

/-- A real compiled return to an installed location supplies its exact costed
prefix. Only the location-validity protocol is additional to FlattenHyps. -/
theorem flatten_return_weighted {F : Type}
    (source : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (reg sectionValue labelValue pc : Nat) (flag : Bool) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (encoded : LabProgHOL 64)
    (hyps : FlattenHyps (.ret reg) source flag result post sectionId labelId continues breaks start)
    (returnValue : StackSemStateOps.getVar reg source = some (.loc sectionValue labelValue))
    (destination : locToPc sectionValue labelValue start.code = some pc) :
    result = some (.result (.loc sectionValue labelValue)) ∧
      stateRel post (updPc pc start) ∧
      LabToTarget.WeightedInstructionTrace encoded { start with clock := start.clock + 1 }
        (updPc pc start) 1 := by
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_ret, returnValue] at evaluated
  simp only [Prod.mk.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  have fetch : asmFetchAux start.pc start.code = some (.asm (.asmi (.jumpReg reg)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, control_appList] using installed)
  exact ⟨rfl, related, jumpreg_update_weighted start encoded reg sectionValue labelValue pc
    fetch (InstCorrect.regOfLookup related returnValue) destination⟩

#print axioms jumpreg_update_weighted
#print axioms flatten_return_weighted
#print axioms flatten_break_weighted
#print axioms flatten_locvalue_weighted
end InitECandidate.Runtime.StackToLab
