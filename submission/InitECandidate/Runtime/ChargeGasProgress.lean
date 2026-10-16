import InitECandidate.Runtime.ChargeGas
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Under the actual funding bound, positive charging advances used gas in
natural arithmetic; modular word arithmetic cannot conceal a decrease. -/
theorem GasFunding.charge_used_growth (funding : GasFunding) (amount : BitVec 64)
    (budget : funding.potential ≤ 200000000) (enough : amount ≤ funding.left) :
    (funding.charge amount).used.toNat = funding.used.toNat + amount.toNat := by
  have total : funding.left.toNat + funding.used.toNat ≤ 200000000 := by
    unfold GasFunding.potential at budget
    omega
  have noWrap := charge_noWrap funding.left funding.used amount enough total
  simp only [GasFunding.charge,BitVec.toNat_add,Nat.mod_eq_of_lt noWrap]

/-- Actual successful charge_gas execution makes positive progress in the
funding measure while retaining its exact source run and memory relation. -/
theorem chargeGas_positive_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) (enough : amount ≤ funding.left)
    (positive : 0 < amount.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_charge_gas) =
        (some (.returned (.val (.word 0))),post) ∧
      HasGasFunding post frame (funding.charge amount) ∧
      (funding.charge amount).potential = funding.potential ∧ post.clock = state.clock ∧
      funding.used.toNat + 1 ≤ (funding.charge amount).used.toNat ∧
      (funding.charge amount).used.toNat ≤ 200000000 := by
  obtain ⟨post,run,related,potential,clock⟩ := chargeGas_preserves_funding state frame amount funding
    hFrame hAmount leftDomain usedDomain memory budget enough
  have growth := funding.charge_used_growth amount budget enough
  have usedBound : (funding.charge amount).used.toNat ≤ 200000000 := by
    have chargedBudget : (funding.charge amount).potential ≤ 200000000 := by rwa [potential]
    unfold GasFunding.potential at chargedBudget
    omega
  exact ⟨post,run,related,potential,clock,by omega,usedBound⟩

#print axioms GasFunding.charge_used_growth
#print axioms chargeGas_positive_progress
end InitECandidate.Runtime
