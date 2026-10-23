import InitE.Challenge
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock

/-!
# Op 3 (Challenge A): finite-`K` bridge for `InitE.Certificate`

Light-weight reduction (imports only `InitE.Challenge`): a finite certificate
`InitE.Certificate s (.finite N)` follows from

1. exact behaviour preservation (the same premise as
   `InitE.certificate_of_exact_behaviour`, already discharged for the vanilla
   baseline by `InitE.full_baseline_correct`), and
2. a *uniform clock bound*: on every in-scope input (declared gas limit
   `≤ 200000000`, terminating source, covered outcome) the target evaluator has
   a non-`timeOut` result at some clock `k ≤ N`.

Point 2 is the only open mathematical obligation; it is where the
`PanToTarget` clock transfer and the software-crypto worst-case step bounds
must land. No new axiom, no `sorry`.
-/

namespace InitECandidate.Solver.FiniteKBridge

open InitE
open Flapjack

/-- The in-scope inputs of the challenge contract. -/
def InScope (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent) : Prop :=
  Guest.GasLimit.declaredGasLimit input ≤ 200000000 ∧
    sourceBehaviour input = .terminate outcome events ∧ coveredOutcome outcome

/-- Clock monotonicity: a non-`timeOut` result at `k ≤ N` persists at `N`. -/
theorem not_timeOut_mono {S Q σ : Type} (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ)
    (ms : S) {k N : Nat} (hk : k ≤ N)
    (h : (evaluateTargetHOL mc ffi k ms).1 ≠ .timeOut) :
    evaluateTargetHOL mc ffi N ms = evaluateTargetHOL mc ffi k ms := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases hrun : evaluateTargetHOL mc ffi k ms with ⟨r, ms1, ffi1⟩
  rw [hrun] at h
  exact evaluateTargetAddClock mc ffi k ms extra r ms1 ffi1 hrun h

/-- Core step: exact behaviour + non-`timeOut` at clock `N` gives a matching
halting execution at exactly `N` steps. The `.error` branch is excluded because
it would be a `.fail` behaviour, contradicting the source's `.terminate`. -/
theorem matchingExecution_of_not_timeOut (s : Submission) (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent) (covered : coveredOutcome outcome)
    (correct : ∀ behaviour, machineSemHOL s.machineConfig (sourceFfi input)
      (s.initialState input) behaviour → behaviour = .terminate outcome events)
    (N : Nat)
    (hnt : (evaluateTargetHOL s.machineConfig (sourceFfi input) N
      (s.initialState input)).1 ≠ .timeOut) :
    matchingExecutionAt s input outcome events N := by
  rcases hrun : evaluateTargetHOL s.machineConfig (sourceFfi input) N
      (s.initialState input) with ⟨r, post, finalFfi⟩
  rw [hrun] at hnt
  cases r with
  | timeOut => exact absurd rfl hnt
  | error =>
    have hfail : machineSemHOL s.machineConfig (sourceFfi input) (s.initialState input)
        .fail := ⟨N, by rw [hrun]⟩
    cases correct _ hfail
  | halt o =>
    have hterm : machineSemHOL s.machineConfig (sourceFfi input) (s.initialState input)
        (.terminate o finalFfi.ioEvents) := ⟨N, post, finalFfi, hrun, rfl⟩
    have heq := correct _ hterm
    cases heq
    exact ⟨outcome, post, finalFfi, hrun, matchingResult_refl input outcome _ covered⟩

/-- **Finite-`K` bridge.** Exact behaviour preservation plus a uniform clock bound
`∃ k ≤ N, ¬timeOut` on in-scope inputs yields `InitE.Certificate s (.finite N)`. -/
theorem certificate_finite_of_exact_behaviour (s : Submission) (N : Nat)
    (score : s.K = .finite N) (admitted : s.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL s.machineConfig (sourceFfi input)
        (s.initialState input) behaviour → behaviour = .terminate outcome events)
    (clock : ∀ input outcome events, InScope input outcome events →
      ∃ k, k ≤ N ∧ (evaluateTargetHOL s.machineConfig (sourceFfi input) k
        (s.initialState input)).1 ≠ .timeOut) :
    Certificate s (.finite N) := by
  refine ⟨score, admitted, ?_⟩
  intro input hgas outcome events source covered
  obtain ⟨k, hk, hnt⟩ := clock input outcome events ⟨hgas, source, covered⟩
  have hN := not_timeOut_mono s.machineConfig (sourceFfi input) (s.initialState input) hk hnt
  refine ⟨N, Nat.le_refl N, ?_⟩
  apply matchingExecution_of_not_timeOut s input outcome events covered
    (correct input outcome events source) N
  rw [hN]; exact hnt

/-- Pipeline form of the clock obligation: if the target halts within
`B + T k_src` steps where `k_src` is a source clock bounded by `G` on in-scope
inputs and `T` is monotone, the bridge applies with `N = B + T G`.
This is the shape of `bootstrap + PanToTarget` clock transfer
(`T k = C_t * (C_b * (C_f * k + D_f) + D_b)` in the fast-dev solver). -/
theorem certificate_finite_of_pipeline (s : Submission) (B G : Nat) (T : Nat → Nat)
    (Tmono : ∀ a b, a ≤ b → T a ≤ T b)
    (score : s.K = .finite (B + T G)) (admitted : s.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL s.machineConfig (sourceFfi input)
        (s.initialState input) behaviour → behaviour = .terminate outcome events)
    (transfer : ∀ input outcome events, InScope input outcome events →
      ∃ kSrc, kSrc ≤ G ∧ (evaluateTargetHOL s.machineConfig (sourceFfi input) (B + T kSrc)
        (s.initialState input)).1 ≠ .timeOut) :
    Certificate s (.finite (B + T G)) := by
  apply certificate_finite_of_exact_behaviour s _ score admitted correct
  intro input outcome events hin
  obtain ⟨kSrc, hk, hnt⟩ := transfer input outcome events hin
  exact ⟨B + T kSrc, Nat.add_le_add_left (Tmono _ _ hk) B, hnt⟩

/-- The linear pass-composition clock map used by the fast-dev solver. -/
def linearTransfer (cf df cb db ct : Nat) (k : Nat) : Nat := ct * (cb * (cf * k + df) + db)

theorem linearTransfer_mono (cf df cb db ct : Nat) :
    ∀ a b, a ≤ b → linearTransfer cf df cb db ct a ≤ linearTransfer cf df cb db ct b := by
  intro a b h
  unfold linearTransfer
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _)) _)

end InitECandidate.Solver.FiniteKBridge
