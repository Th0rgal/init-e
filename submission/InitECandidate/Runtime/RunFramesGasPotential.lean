import InitECandidate.Runtime.RunFramesOpAddLoop
import InitECandidate.Runtime.NodedbInputCost
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Runtime.FineCost

/-- A finite chain of real ADD iterations of the actual `run_frames` loop body.
Each step records the evaluator result and the exact funding relation of the
charge made by the body, so the gas measure can be followed without assuming a
program-level cost oracle. -/
inductive RunFramesAddIterations (frame : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory → GasFunding →
      Nat → PanSemStateFiniteExact 64 Guest.HostMemory → GasFunding → Prop where
  | zero (state : PanSemStateFiniteExact 64 Guest.HostMemory) (funding : GasFunding) :
      RunFramesAddIterations frame state funding 0 state funding
  | step (state next post : PanSemStateFiniteExact 64 Guest.HostMemory)
      (funding final : GasFunding) (count : Nat)
      (body : evaluateHOLFiniteState state runFramesLoopBody = (none, next))
      (funded : HasGasFunding next frame (funding.charge 3))
      (budget : funding.potential ≤ 200000000)
      (enough : (3 : BitVec 64) ≤ funding.left)
      (tail : RunFramesAddIterations frame next (funding.charge 3) count post final) :
      RunFramesAddIterations frame state funding (count + 1) post final

/-- The gas-decreasing potential of the ADD loop: every recorded iteration moves
exactly three units from gas-left to regular-gas-used, so the consumed gas is
`3 * count` and the total funded potential is conserved. -/
theorem RunFramesAddIterations.accounting {frame : BitVec 64}
    {state post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {funding final : GasFunding} {count : Nat}
    (trace : RunFramesAddIterations frame state funding count post final) :
    final.left.toNat + 3 * count = funding.left.toNat ∧
    final.used.toNat = funding.used.toNat + 3 * count ∧
    final.potential = funding.potential := by
  induction trace with
  | zero state funding =>
      simp
  | step state next post funding final count body funded budget enough tail ih =>
      obtain ⟨ihLeft, ihUsed, ihPotential⟩ := ih
      have chargePotential := funding.charge_potential 3 budget enough
      have chargeUsed := funding.charge_used_growth 3 budget enough
      have hthree : (3 : BitVec 64).toNat = 3 := by decide
      have chargeLeft : (funding.charge 3).left.toNat + 3 = funding.left.toNat := by
        unfold GasFunding.potential at chargePotential
        have spill : (funding.charge 3).spilled = funding.spilled := rfl
        rw [chargeUsed, spill, hthree] at chargePotential
        omega
      refine ⟨?_, ?_, ?_⟩
      · omega
      · omega
      · rw [ihPotential, chargePotential]

/-- Total executed work is the gas-dependent loop work plus any
gas-independent input and witness preparation recorded separately. The latter
does not consume the frame's gas-left counter and therefore simply adds to the
budget. -/
def guestIndependentWork (inputLimit witnessCost : Nat) : Nat :=
  nodedbInputCallCost inputLimit + witnessCost

/-- Uniform ceiling for a completed ADD loop: the loop cannot consume more than
the frame's whole funded potential, independent of the number of iterations or
of the input/witness work. -/
theorem RunFramesAddIterations.work_le_budget {frame : BitVec 64}
    {state post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {funding final : GasFunding} {count : Nat}
    (trace : RunFramesAddIterations frame state funding count post final)
    (budget : funding.potential ≤ 200000000) (witnessCost : Nat) :
    3 * count + guestIndependentWork 0 witnessCost ≤ 200000000 + guestIndependentWork 0 witnessCost := by
  obtain ⟨left, _, potential⟩ := trace.accounting
  have usedLe : 3 * count ≤ funding.left.toNat := by omega
  have leftLe : funding.left.toNat ≤ funding.potential := by
    unfold GasFunding.potential
    omega
  have gasLe : 3 * count ≤ 200000000 := by omega
  omega

/-- One actual ADD iteration lowers gas-left by three, raises used by three,
and conserves the funded potential. This is the concrete step consumed by the
iteration accounting above. -/
theorem runFrames_add_loop_gas_decrease (coeff : FineCost.Work)
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation frame sp cap base pc length active : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (lengthDomain : state.memaddrs (frame + 56))
    (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (inv : GuestFrameInvariant state frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (arguments : evalListHOLFinite (runFramesLoopDispatchEntry state pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [runFramesOpcodeExpression] = some [.val (.word (1 : BitVec 64))])
    (clock : 9 ≤ state.clock) (budget : funding.potential ≤ 200000000)
    (enough : (3 : BitVec 64) ≤ funding.left) :
    ∃ post, evaluateHOLFiniteState state runFramesLoopBody = (none, post) ∧
      HasGasFunding post frame (funding.charge 3) ∧
      (funding.charge 3).left.toNat + 3 = funding.left.toNat ∧
      (funding.charge 3).used.toNat = funding.used.toNat + 3 ∧
      (funding.charge 3).potential = funding.potential := by
  obtain ⟨post, body, funded, _, _, _, growth⟩ :=
    runFrames_add_loop_progress coeff state continuation frame sp cap base pc length active
      funding a0 a1 a2 a3 b0 b1 b2 b3 contGlobal pendingDomain pendingMemory activeDomain
      activeMemory running lengthDomain lengthMemory inside inv arguments clock budget
  have chargePotential := funding.charge_potential 3 budget enough
  have chargeUsed := funding.charge_used_growth 3 budget enough
  have hthree : (3 : BitVec 64).toNat = 3 := by decide
  have chargeLeft : (funding.charge 3).left.toNat + 3 = funding.left.toNat := by
    unfold GasFunding.potential at chargePotential
    have spill : (funding.charge 3).spilled = funding.spilled := rfl
    rw [chargeUsed, spill, hthree] at chargePotential
    omega
  exact ⟨post, body, funded, chargeLeft, by simpa using growth, chargePotential⟩

#print axioms RunFramesAddIterations.accounting
#print axioms RunFramesAddIterations.work_le_budget
#print axioms runFrames_add_loop_gas_decrease
end InitECandidate.Runtime
