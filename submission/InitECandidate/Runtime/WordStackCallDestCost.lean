import InitECandidate.Runtime.WordStackCallFrameCost
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Direct calls need no destination load; indirect calls need at most one.
This includes the compiler's guarded empty-argument fallback. -/
theorem wordStack_callDest_cost {F : Type} (dest : Option Nat) (args : List Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (callDestNative dest args kf).1 source ≤ 7 := by
  cases dest with
  | some pos => simp [callDestNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  | none =>
    simp only [callDestNative]
    split
    · simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]
    · dsimp only [WordToStackRegFormat.wReg2]
      split
      · simp [wStackLoadNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]
      · have offset : kf.2.1 - 1 - (args.getLast (by intro empty; have zero : args.length = 0 := congrArg List.length empty; contradiction) / 2 - kf.1) ≤ 91 := by omega
        have bound := wordStackLoad_cost
          [(kf.1 + 1, kf.2.1 - 1 - (args.getLast (by intro empty; have zero : args.length = 0 := congrArg List.length empty; contradiction) / 2 - kf.1))]
          .skip 0 (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact offset)
          (fun state => by simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]) source
        simpa only [List.length_singleton, Nat.mul_one, Nat.add_zero] using bound

#print axioms wordStack_callDest_cost
end InitECandidate.Runtime.WordToStack
