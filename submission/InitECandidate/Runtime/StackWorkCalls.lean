import InitECandidate.Runtime.StackWork
import InitECandidate.Runtime.StackToLabCall
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Call

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

section
variable {width : Nat} [NeZero width] {C F : Type}
theorem stackWork_tailCall_bound (s1 : StackSemStateFiniteExact width C F) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ih : ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      MeasureLt p s (.call none dest handler) s1 → BoundedFlattenProp p s (stackWork p s)) :
    BoundedFlattenProp (.call none dest handler) s1 (stackWork (.call none dest handler) s1) := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have fetch : asmFetchAux t1.pc t1.code = some (Flapjack.Compiler.Backend.StackToLab.compileJumpHOL dest) :=
    fetchSingle (Prelude.notIsLabelCompileJump dest)
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hfind : StackSemControl.findCode dest s1.regs s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  rcases handler with _ | hd
  swap; · exact (err ev).elim
  simp only at ev
  obtain ⟨d, pc', -, entry, caP, instP, step⟩ :=
    compileJumpEnter (fun r v h => InstCorrect.regOfLookup rel h) rel fetch hfind
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.zero_le _, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have lt : MeasureLt prog (StackSemStateOps.decClock s1) (.call none dest none) s1 :=
    .inl (by simp [StackSemStateOps.decClock]; omega)
  have ph := ih prog _ lt true (some x') s' d (Flapjack.Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []
    { t1 with pc := pc', clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
  refine boundedFlattenConcl_mono (a := 0 + stackWork prog (StackSemStateOps.decClock s1)) ?_ ?_
  · simp only [stackWork, if_neg h0, hfind]
    omega
  · exact boundedComposeSome 0 (stackWork prog (StackSemStateOps.decClock s1)) (by decide) (runEnter (by omega) step) rfl rfl rfl rfl rfl
      (List.prefix_refl _)
      (boundedFlattenConclResult (budget := stackWork prog (StackSemStateOps.decClock s1)) (p' := prog) (t' := true) (l' := 0) (h := ph) rfl
        (resultViewIndep hbad _ _ _ _ _ _))
end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.stackWork_tailCall_bound
