import InitE.Challenge

namespace InitECandidate.Runtime
open InitE Flapjack
open Flapjack.PanSemStateFiniteExact
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Declaration installation followed by the authoritative Pancake entry call.
The clock is source loop/call fuel, not a count of all syntax nodes or RISC-V steps. -/
noncomputable def sourceTerminatesAt (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent) (fuel : Nat) : Prop := by
  classical
  exact ∃ context, ∃ (installed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : PanSemResultExact 64) (finalState : PanSemStateFiniteExact 64 Guest.HostMemory),
    decsStcnamesHOLExact [] (Guest.guestAst.map declToHOL) = some context ∧
    evaluateDeclsHOLFinite { sourceInitialState input with structs := context }
      (Guest.guestAst.map declToHOL) = some installed ∧
    evaluateHOLFiniteState { installed with clock := fuel }
      (.call none (ofString "main") []) = (some result, finalState) ∧
    (match result with
      | .finalFfi ffi => outcome = HolOutcome.ffiOutcome ffi
      | .returned _ => outcome = .success
      | _ => False) ∧
    finalState.ffi.ioEvents = events

/-- Covered source termination already provides some finite source fuel.
A uniform numerical ceiling is a separate obligation. -/
theorem sourceTerminatesAt_exists (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (h : sourceBehaviour input = .terminate outcome events) :
    ∃ fuel, sourceTerminatesAt input outcome events fuel := by
  classical
  unfold sourceBehaviour PanSemStateFiniteExact.semanticsDecls at h
  split at h
  · cases h
  · rename_i context hc
    split at h
    · cases h
    · rename_i installed hi
      unfold PanSemStateFiniteExact.semantics at h
      dsimp only at h
      split at h
      · cases h
      · split at h
        · rename_i chosen choice
          obtain ⟨fuel, finalState, result, actualOutcome, run, terminal, trace⟩ :=
            holOptionSome_some choice
          rw [h] at trace
          have eqs := HolBehaviour.terminate.inj trace
          rcases eqs with ⟨rfl, eventEq⟩
          cases result with
          | none => simp at terminal
          | some result =>
            refine ⟨fuel, context, installed, result, finalState, hc, hi, run, ?_, eventEq.symm⟩
            cases result <;> simpa using terminal
        · cases h

/-- A quantitative source bound must apply to every covered terminating input,
including malformed requests. Input length is not a certificate assumption. -/
def SourceBound (bound : Guest.InputBlob → Nat) : Prop :=
  ∀ input, Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
    ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      ∃ fuel, fuel ≤ bound input ∧ sourceTerminatesAt input outcome events fuel

/-- The missing quantitative compiler property. This includes bootstrap and
preserves the challenge observation, rather than merely target termination. -/
def AffineTransfer (submission : Submission) (scale overhead : Nat) : Prop :=
  ∀ input outcome events fuel,
    sourceBehaviour input = .terminate outcome events →
    coveredOutcome outcome →
    sourceTerminatesAt input outcome events fuel →
    ∃ steps, steps ≤ scale * fuel + overhead ∧
      matchingExecutionAt submission input outcome events steps

/-- Compose independently proved source, compiler and uniform bounds.
No quantitative compiler or gas invariant is assumed implicitly. -/
theorem certificate_of_bounds (submission : Submission)
    (scale overhead ceiling : Nat) (bound : Guest.InputBlob → Nat)
    (score : submission.K = .finite (scale * ceiling + overhead))
    (admitted : submission.Admitted) (source : SourceBound bound)
    (uniform : ∀ input, Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      bound input ≤ ceiling)
    (compiler : AffineTransfer submission scale overhead) :
    Certificate submission (.finite (scale * ceiling + overhead)) := by
  refine ⟨score, admitted, ?_⟩
  intro input gas outcome events behaviour covered
  obtain ⟨fuel, fuelBound, run⟩ := source input gas outcome events behaviour covered
  obtain ⟨steps, stepBound, target⟩ := compiler input outcome events fuel behaviour covered run
  refine ⟨steps, ?_, target⟩
  change steps ≤ scale * ceiling + overhead
  exact stepBound.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left scale (fuelBound.trans (uniform input gas))) overhead)

/-- Change only a participant's claimed score; executable bytes and machine
configuration are definitionally unchanged. -/
def withScore (submission : Submission) (score : NatE) : Submission :=
  { submission with K := score }

theorem withScore_admitted (submission : Submission) (score : NatE)
    (h : submission.Admitted) : (withScore submission score).Admitted := by
  exact ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper,
    h.anchor_aligned, h.name_boundary, h.metadata_length, h.ordinary_slots_loaded,
    h.mmio_valid, h.entry_distinct, h.entry_loaded, h.entry_aligned,
    h.entry_dispatch_separate, h.mmio_program, h.exit_loaded, h.layout_bound⟩

theorem finite_certificate_of_bounds (submission : Submission)
    (scale overhead ceiling : Nat) (bound : Guest.InputBlob → Nat)
    (admitted : submission.Admitted) (source : SourceBound bound)
    (uniform : ∀ input, Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      bound input ≤ ceiling)
    (compiler : AffineTransfer submission scale overhead) :
    Certificate (withScore submission (.finite (scale * ceiling + overhead)))
      (.finite (scale * ceiling + overhead)) := by
  apply certificate_of_bounds _ scale overhead ceiling bound rfl
    (withScore_admitted submission _ admitted) source uniform
  exact compiler

/-- Input contributions must saturate at accessible bytes: arbitrary list
lengths remain admissible, and oversized declarations take the covered trap. -/
def accessibleInputBytes (input : Guest.InputBlob) : Nat :=
  min input.length (inputSize - 16)

theorem accessibleInputBytes_le (input : Guest.InputBlob) :
    accessibleInputBytes input ≤ 134217712 := by
  exact Nat.min_le_right _ _

/-- Arithmetic assembly for a gas-and-input-dependent source bound. -/
theorem gas_input_bound (input : Guest.InputBlob) (gasCost byteCost fixed : Nat)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    gasCost * Guest.GasLimit.declaredGasLimit input +
        byteCost * accessibleInputBytes input + fixed ≤
      gasCost * 200000000 + byteCost * 134217712 + fixed := by
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul_left gasCost gas)
    (Nat.mul_le_mul_left byteCost (accessibleInputBytes_le input))) fixed

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.certificate_of_bounds

#print axioms InitECandidate.Runtime.sourceTerminatesAt_exists
#print axioms InitECandidate.Runtime.finite_certificate_of_bounds
