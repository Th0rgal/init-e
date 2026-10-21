import InitECandidate.Runtime.StackRefinedRemovalMonotone
import InitECandidate.Runtime.GuestSpillPrices
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Pointwise local-price compatibility for retaining conservative frame and
call setup charges while tightening recursive body instruction prices. -/
class ConservativeRemovalPrice (price : HolProg 64 → Nat) : Prop where
  le : ∀ p, price p ≤ removalLocalPrice 6 riscvConfig.addrOffset p

instance conservativeRemovalPrice_original :
    ConservativeRemovalPrice (removalLocalPrice 6 riscvConfig.addrOffset) := ⟨fun _ => Nat.le_refl _⟩

instance conservativeRemovalPrice_refined :
    ConservativeRemovalPrice (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) :=
  ⟨refinedRemovalLocalPrice_le 6 riscvConfig.addrOffset⟩

namespace ConservativeRemovalPrice
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

theorem freeSeq (a b : HolProg 64) : price (.seq a b) = 0 := by
  have bound := caps.le (.seq a b)
  exact Nat.eq_zero_of_le_zero bound

theorem skip : price .skip = 0 := Nat.eq_zero_of_le_zero (caps.le .skip)

theorem alloc (count : Nat) (small : count ≤ 92) : price (.stackAlloc count) ≤ 25 :=
  (caps.le _).trans (guest_frame_alloc_price count small)

theorem free (count : Nat) (small : count ≤ 92) : price (.stackFree count) ≤ 7 :=
  (caps.le _).trans (guest_frame_free_price count small)

theorem execution {F : Type} (program : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p) program source ≤
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) program source :=
  stackExecutionCost_mono _ _ (fun p _ => caps.le p) program source

end ConservativeRemovalPrice
#print axioms ConservativeRemovalPrice.freeSeq
#print axioms ConservativeRemovalPrice.skip
#print axioms ConservativeRemovalPrice.alloc
#print axioms ConservativeRemovalPrice.free
#print axioms ConservativeRemovalPrice.execution
end InitECandidate.Runtime.StackToLab
