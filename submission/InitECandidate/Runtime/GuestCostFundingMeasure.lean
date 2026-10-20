import InitECandidate.Runtime.GuestCostGasBudget
import InitECandidate.Runtime.ChargeGasCallFootprint
import InitECandidate.Runtime.ChargeGasProgress
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The consumed-gas measure read from one live frame record: the regular-gas
`used` counter at offset 184. This is an executed-work quantity debitied by the
real `charge_gas` helper, unlike the Pancake call/loop clock, which is only a
termination index. -/
def guestFrameUsed {σ : Type} [NeZero 64] (state : PanSemStateFiniteExact 64 σ)
    (frame : BitVec 64) : Nat :=
  match state.memory (frame + 184) with
  | .word used => used.toNat

/-- The frame's used counter as a function of the memory map, for `while_gas_budget_memory`. -/
def guestUsedRead (frame : BitVec 64) : (RiscV.Word 64 → HolWordLab 64) → Nat :=
  fun memory => match memory (frame + 184) with
    | .word used => used.toNat

theorem guestFrameUsed_eq_read {σ : Type} [NeZero 64]
    (state : PanSemStateFiniteExact 64 σ) (frame : BitVec 64) :
    guestFrameUsed state frame = guestUsedRead frame state.memory := rfl

/-- Under the funding relation the memory cell is exactly the funding counter. -/
theorem guestFrameUsed_eq_funding {σ : Type} [NeZero 64]
    {state : PanSemStateFiniteExact 64 σ} {frame : BitVec 64} {funding : GasFunding}
    (memory : HasGasFunding state frame funding) :
    guestFrameUsed state frame = funding.used.toNat := by
  unfold guestFrameUsed
  rw [memory.2.1]

/-- The measure is bounded by the declared regular-gas budget: consumed gas can
never exceed the funded potential. -/
theorem guestFrameUsed_le_budget {σ : Type} [NeZero 64]
    {state : PanSemStateFiniteExact 64 σ} {frame : BitVec 64} {funding : GasFunding}
    (memory : HasGasFunding state frame funding) (budget : funding.potential ≤ 200000000) :
    guestFrameUsed state frame ≤ 200000000 := by
  rw [guestFrameUsed_eq_funding memory]
  unfold GasFunding.potential at budget
  omega

/-- An actual successful `charge_gas` call advances the consumed-gas measure by
exactly the charged amount, and therefore by at least one unit whenever the
charge is positive. This is the progress half of the loop contract, taken from
the real evaluator footprint rather than assumed. -/
theorem charge_gas_call_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (frame amount : BitVec 64) (funding : GasFunding)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word amount)])
    (installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount", .one)], sourceFunctionBody Guest.guestFn_charge_gas, .one))
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) (enough : amount ≤ funding.left) :
    evaluateHOLFiniteState state (.call (some (none, none)) (ofString "charge_gas") [argument]) =
      (none, chargeGasCallPost state frame funding amount) ∧
    HasGasFunding (chargeGasCallPost state frame funding amount) frame (funding.charge amount) ∧
    guestFrameUsed (chargeGasCallPost state frame funding amount) frame =
      guestFrameUsed state frame + amount.toNat ∧
    guestFrameUsed (chargeGasCallPost state frame funding amount) frame ≤ 200000000 := by
  have run := evaluate_chargeGas_call state argument frame amount funding arguments installed
    clock hFrame leftDomain usedDomain memory enough
  refine ⟨run, ?_, ?_, ?_⟩
  · exact chargeGasCallPost_funding state frame amount funding memory
  · have growth := funding.charge_used_growth amount budget enough
    rw [guestFrameUsed_eq_funding memory]
    rw [guestFrameUsed_eq_funding (chargeGasCallPost_funding state frame amount funding memory)]
    exact growth
  · exact guestFrameUsed_le_budget
      (chargeGasCallPost_funding state frame amount funding memory)
      (by rw [funding.charge_potential amount budget enough]; exact budget)

/-- The same call makes positive progress: a strictly positive charge raises the
measure by at least one, which is exactly the `mu state + 1 <= mu middle`
premise of `GasAmortizedBody`. -/
theorem charge_gas_call_positive_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (frame amount : BitVec 64) (funding : GasFunding)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word amount)])
    (installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount", .one)], sourceFunctionBody Guest.guestFn_charge_gas, .one))
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) (enough : amount ≤ funding.left)
    (positive : 0 < amount.toNat) :
    guestFrameUsed state frame + 1 ≤ guestFrameUsed (chargeGasCallPost state frame funding amount) frame := by
  obtain ⟨_, _, advance, _⟩ := charge_gas_call_progress state argument frame amount funding
    arguments installed clock hFrame leftDomain usedDomain memory budget enough
  omega

/-- Amortized loop budget stated directly in the guest's consumed-gas measure,
restricted to the allowed (funded, laid-out, reachable) states `I`:
the loop's executed work is at most `(C + B + D) * (used increase) + (B + D)`,
where `B` is the per-run terminal/rejection prefix that need not have charged
gas, and the global funding budget turns the increase into a uniform ceiling. -/
theorem guest_loop_gas_budget (coeff : Work) (C B D : Nat) (frame : BitVec 64)
    (I : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (clockStep : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,
      I state → I (decClockHOLFinite state))
    {s : PanSemStateFiniteExact 64 Guest.HostMemory} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {events : List WorkEvent}
    (run : StatementRun s (.while condition body) r post events)
    (initial : I s)
    (amortized : @GasAmortizedBody Guest.HostMemory coeff condition body I
      (fun state => guestFrameUsed state frame) C B D) :
    coeff.score (executionWork events) ≤
      (C + B + D) * (guestFrameUsed post frame - guestFrameUsed s frame) + (B + D) ∧
    guestFrameUsed s frame ≤ guestFrameUsed post frame :=
  while_gas_budget_memory coeff (guestUsedRead frame) I C B D clockStep run initial amortized

#print axioms charge_gas_call_progress
#print axioms charge_gas_call_positive_progress
#print axioms guestFrameUsed_le_budget
#print axioms guest_loop_gas_budget
end InitECandidate.Runtime.FineCost
