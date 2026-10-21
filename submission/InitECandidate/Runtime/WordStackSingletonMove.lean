import InitECandidate.Runtime.WordStackMoveCost
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- A single parallel move cannot form a nontrivial cycle. -/
theorem parmove_singleton {α : Type} [DecidableEq α] (dst src : α) :
    Parmove.parmove [(dst, src)] = if dst = src then [] else [(some dst, some src)] := by
  by_cases equal : dst = src
  · subst src
    simp [Parmove.parmove, Parmove.pmov, Parmove.fstep]
  · simp [Parmove.parmove, Parmove.pmov, Parmove.fstep, Parmove.splitSource, equal, Ne.symm equal]

/-- The variable-assignment selector emits one move, not a general cyclic
parallel shuffle. Its lowering needs at most one load and one store. -/
theorem wordStack_singleton_move_cost {F : Type} (dst src : Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveNative [(dst,src)] kf) source ≤ 14 := by
  simp only [wMoveNative, List.map_cons, List.map_nil, parmove_singleton]
  split
  · simp [wMoveAuxNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  · simpa only [List.map_cons, List.map_nil, wMoveAuxNative] using
      wordStack_move_single_cost
        (WordToStackRegFormat.formatVar kf.1 (some (dst/2)),
          WordToStackRegFormat.formatVar kf.1 (some (src/2))) kf small source

theorem executedSimulation_singleton_move {F : Type}
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64) (priority dst src : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.move priority [(dst,src)]) source 14 := by
  apply executedSimulation_of_fragment ac (.move priority [(dst,src)]) source 14
    (Flapjack.WordToStackProofs.CompCorrect.MoveFull.compCorrectMove ac priority [(dst,src)] source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_singleton_move_cost dst src (k,f,frame) small target

#print axioms parmove_singleton
#print axioms wordStack_singleton_move_cost
#print axioms executedSimulation_singleton_move
end InitECandidate.Runtime.WordToStack
