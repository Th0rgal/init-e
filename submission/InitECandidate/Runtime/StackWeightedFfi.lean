import InitECandidate.Runtime.StackWeightedTerminal
import InitECandidate.Runtime.StackWeightedControl
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Ffi
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- A returned external call pays the actual return-label materialization and
one host-call allowance. Reads, FFI response and successor state are derived
from the actual source evaluation and original compiler ABI premises. -/
theorem normalWeightedFlatten_ffi {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) :
    NormalWeightedFlatten (.ffi name ptr len ptr2 len2 ret) source
      (fun encoded pc => LabToTarget.controlWork 2 encoded pc + 17) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ffi] at evaluated
  simp only [StackProps.callArgs] at args
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := args
  have hinst : codeInstalled start.pc [.labAsm (.locValue start.linkReg (.lab sectionId labelId)) 0 [] 0,
      .labAsm (.callFFI name) 0 [] 0, .label sectionId labelId 0] start.code := by
    simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed
  simp only [isLabelHOL, Bool.false_eq_true, if_false, if_true, codeInstalled] at hinst
  obtain ⟨fetch0, fetch1, locL, _⟩ := hinst
  obtain ⟨_, _, hmem, hdom, _, hbe, hffiEq, _, _, _, _, _, d13, d14, d15, d16, _⟩ := id related
  split at evaluated
  · rename_i w w2 w3 w4 hlen hptr hlen2 hptr2
    have rlen := InstCorrect.regOfLookup related hlen
    have rptr := InstCorrect.regOfLookup related hptr
    have rlen2 := InstCorrect.regOfLookup related hlen2
    have rptr2 := InstCorrect.regOfLookup related hptr2
    split at evaluated
    · rename_i cfg bytes hcfg hbytes
      rw [← hmem, ← hdom, ← hbe] at hcfg hbytes
      rw [← hffiEq] at evaluated
      split at evaluated
      · simp at evaluated
      · rename_i newFfi returned hffi
        simp only [Prod.mk.injEq, true_and] at evaluated
        subst post
        let mid : LabSem.State 64 LabToTarget.Config F :=
          {incPc (updReg start.linkReg (.loc sectionId labelId) start) with clock := start.clock + 1}
        let final := LabToTarget.ffiReturnedSource mid name w4 returned (start.pc + 2) newFfi
        have before := (locvalue_update_weighted start encoded start.linkReg (.lab sectionId labelId)
          (start.pc + 2) fetch0 locL).toMixed.add_clock 1
        have callTrace : LabToTarget.WeightedMixedTrace encoded mid final 17 := by
          have step := LabToTarget.WeightedMixedTrace.ffi (code := encoded) mid final name 0 [] 0
            w w2 w3 w4 cfg bytes sectionId labelId (start.pc + 2) newFfi returned 0
            (by dsimp only [mid]; omega)
            (by simpa only [mid, asmFetch, incPc, updReg] using fetch1)
            (by simpa only [mid, incPc, updReg, Ne.symm d13, if_false] using rlen)
            (by simpa only [mid, incPc, updReg, Ne.symm d14, if_false] using rptr)
            (by simpa only [mid, incPc, updReg, Ne.symm d15, if_false] using rlen2)
            (by simpa only [mid, incPc, updReg, Ne.symm d16, if_false] using rptr2)
            hcfg hbytes
            (by simp [mid, incPc, updReg]) locL hffi (.nil final)
          simpa only [Nat.zero_add] using step
        have joined := LabToTarget.weightedMixedTrace_append before callTrace
        refine ⟨final, 2, LabToTarget.controlWork 2 encoded start.pc + 17, ?_, ?_, rfl,
          Nat.le_refl _, ?_⟩
        · have rel := stateRelFfiRet related name start.linkReg rfl (.loc sectionId labelId)
            (writeBytearrayExact w4 returned start.memory start.memDomain start.be) newFfi (start.pc + 2)
          simpa [final, mid, LabToTarget.ffiReturnedSource, incPc, updReg, hmem, hdom, hbe] using rel
        · simp [final, mid, LabToTarget.ffiReturnedSource, Flapjack.Compiler.Backend.StackToLab.flattenHOL,
            appListAppendList, isLabelHOL]
        · simpa only [Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl, labToLoc] using joined
    · simp at evaluated
  · simp at evaluated

/-- A terminal external call pays return-label materialization in the prefix;
the shared terminal extraction adds its final allowance exactly once. -/
theorem terminalWeightedFlatten_ffi {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (event : HolFinalEvent) :
    TerminalWeightedFlatten (.ffi name ptr len ptr2 len2 ret) source (.finalFFI event)
      (.ffiOutcome event) (fun encoded pc => LabToTarget.controlWork 2 encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, nonerror, related, args, installed, labels⟩
  rw [StackSemEvaluate.evaluate_ffi] at evaluated
  simp only [StackProps.callArgs] at args
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := args
  have hinst : codeInstalled start.pc [.labAsm (.locValue start.linkReg (.lab sectionId labelId)) 0 [] 0,
      .labAsm (.callFFI name) 0 [] 0, .label sectionId labelId 0] start.code := by
    simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed
  simp only [isLabelHOL, Bool.false_eq_true, if_false, if_true, codeInstalled] at hinst
  obtain ⟨fetch0, fetch1, locL, _⟩ := hinst
  obtain ⟨_, _, hmem, hdom, _, hbe, hffiEq, _, _, _, _, _, d13, d14, d15, d16, _⟩ := id related
  split at evaluated
  · rename_i w w2 w3 w4 hlen hptr hlen2 hptr2
    have rlen := InstCorrect.regOfLookup related hlen
    have rptr := InstCorrect.regOfLookup related hptr
    have rlen2 := InstCorrect.regOfLookup related hlen2
    have rptr2 := InstCorrect.regOfLookup related hptr2
    split at evaluated
    · rename_i cfg bytes hcfg hbytes
      rw [← hmem, ← hdom, ← hbe] at hcfg hbytes
      rw [← hffiEq] at evaluated
      split at evaluated
      · rename_i outcome hffi
        simp only [Prod.mk.injEq, Option.some.injEq, StackSemResult.finalFFI.injEq] at evaluated
        obtain ⟨rfl, rfl⟩ := evaluated
        let mid : LabSem.State 64 LabToTarget.Config F :=
          {incPc (updReg start.linkReg (.loc sectionId labelId) start) with clock := start.clock + 1}
        have before := (locvalue_update_weighted start encoded start.linkReg (.lab sectionId labelId)
          (start.pc + 2) fetch0 locL).toMixed.add_clock 1
        refine ⟨mid, 2, LabToTarget.controlWork 2 encoded start.pc, hffiEq, rfl, Nat.le_refl _, ?_, ?_⟩
        · simpa only [Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl, labToLoc,
            mid, incPc, updReg] using before
        · exact LabToTarget.Terminal.ffi mid name 0 [] 0 w w2 w3 w4 cfg bytes sectionId labelId
            (start.pc + 2) outcome
            (by dsimp only [mid]; omega)
            (by simpa only [mid, asmFetch, incPc, updReg] using fetch1)
            (by simpa only [mid, incPc, updReg, Ne.symm d13, if_false] using rlen)
            (by simpa only [mid, incPc, updReg, Ne.symm d14, if_false] using rptr)
            (by simpa only [mid, incPc, updReg, Ne.symm d15, if_false] using rlen2)
            (by simpa only [mid, incPc, updReg, Ne.symm d16, if_false] using rptr2)
            hcfg hbytes (by simp [mid, incPc, updReg]) locL hffi
      · simp at evaluated
    · simp at evaluated
  · simp at evaluated

#print axioms terminalWeightedFlatten_ffi
#print axioms normalWeightedFlatten_ffi
end InitECandidate.Runtime.StackToLab
