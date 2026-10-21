import InitECandidate.Runtime.StackWeightedControl
import InitECandidate.Runtime.StackWeightedTerminal
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Call
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Only the reached call target is charged: direct jumps cost two native
instructions and indirect jumps cost one. -/
def callJumpWork (dest : Nat ⊕ Nat) : Nat :=
  match dest with | .inl _ => 2 | .inr _ => 1

/-- Enter the actual installed callee, consuming the original source call's
clock unit. No extra label-clock supply or code-size multiplier is needed. -/
theorem compileJumpEnter_weighted {F : Type}
    {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {start : LabSem.State 64 LabToTarget.Config F} {dest : Nat ⊕ Nat}
    {regs : HolFiniteMapExact Nat (WordLocW 64)} {prog : HolProg 64}
    (encoded : LabProgHOL 64)
    (hregs : ∀ r v, regs.lookup r = some v → start.regs r = v)
    (related : stateRel source start) (positive : source.clock ≠ 0)
    (fetch : asmFetchAux start.pc start.code = some (compileJumpHOL dest))
    (found : StackSemControl.findCode dest regs source.code = some prog) :
    ∃ calleeSection pc, sptLookup calleeSection source.code = some prog ∧
      locToPc calleeSection 0 start.code = some pc ∧
      StackProps.callArgs prog start.ptrReg start.lenReg start.ptr2Reg start.len2Reg start.linkReg ∧
      codeInstalled pc (appListAppend
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL true prog calleeSection
          (StackAlloc.nextLabHOL prog 2) [] []).1) start.code ∧
      stateRel (StackSemStateOps.decClock source) {start with pc := pc, clock := start.clock - 1} ∧
      LabToTarget.WeightedMixedTrace encoded start
        {start with pc := pc, clock := start.clock - 1} (callJumpWork dest) := by
  have clock := relClock related
  cases dest with
  | inl calleeSection =>
    have lookup : sptLookup calleeSection source.code = some prog := by
      simpa [StackSemControl.findCode] using found
    obtain ⟨args, pc, installed, entry⟩ := relCode related lookup
    refine ⟨calleeSection, pc, lookup, entry, args, installed, StateRel.stateRelDecClock related, ?_⟩
    have trace := jump_update_weighted (decClock start) encoded (.lab calleeSection 0) pc fetch
      (by simpa [getPcValue, decClock] using entry)
    simpa [decClock, updPc, callJumpWork, show start.clock - 1 + 1 = start.clock by omega] using trace.toMixed
  | inr reg =>
    simp only [StackSemControl.findCode] at found
    split at found
    · rename_i calleeSection read
      obtain ⟨args, pc, installed, entry⟩ := relCode related found
      refine ⟨calleeSection, pc, found, entry, args, installed, StateRel.stateRelDecClock related, ?_⟩
      have trace := jumpreg_update_weighted (decClock start) encoded reg calleeSection 0 pc fetch (hregs reg _ read) entry
      simpa [decClock, updPc, callJumpWork, show start.clock - 1 + 1 = start.clock by omega] using trace.toMixed
    · simp at found

#print axioms compileJumpEnter_weighted
end InitECandidate.Runtime.StackToLab
