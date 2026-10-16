import InitECandidate.Runtime.StackWorkCorrect
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect

/-- Source-derived budget for entry plus a possible final halting procedure. -/
noncomputable def entryWork {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (s : StackSemStateFiniteExact width C F) : Nat :=
  match sptLookup start s.code with
  | none => 0
  | some prog =>
      let returned := StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s)
      stackWork prog (StackSemStateOps.decClock s) +
        match returned.1 with
        | some (.result (.loc n 0)) =>
            match sptLookup n returned.2.code with
            | none => 0
            | some haltProg => stackWork haltProg returned.2
        | _ => 0

/-- HOL `flatten_call_correct`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem flattenEntry_bounded {width : Nat} [NeZero width] {C F : Type} {start : Nat}
    {s1 s2 : StackSemStateFiniteExact width C F} {res : Option (StackSemResult width)}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} :
    StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), s1) = (res, s2) ∧
    stateRel s1 t1 ∧
    locToPc start 0 t1.code = some t1.pc ∧
    res ≠ some .error ∧
    (res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n, res = some (.result (.loc n 0)) ∧
        ∀ s : StackSemStateFiniteExact width C F, sptSubspt s1.code s.code ∧ s.clock ≠ 0 →
          ∃ t, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), s) =
              (some (.halt (.word 0)), t) ∧
            t.ffi = s.ffi ∧ t.clock = s.clock - 1)) →
    ∃ (ck : Nat), ck ≤ entryWork start s1 ∧ ∃ (r2 : MachineResult) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      evaluate { t1 with clock := t1.clock - 1 + ck } = (r2, t2) ∧
      (∀ f, res = some (.finalFFI f) → r2 = .halt (.ffiOutcome f)) ∧
      (∀ w, res = some (.halt w) → r2 =
        match w with
        | .word w => if w = 0 then .halt .success else .halt .resourceLimitHit
        | _ => .error) ∧
      (∀ n, res = some (.result (.loc n 0)) → r2 = .halt .success) ∧
      t2.ffi = s2.ffi ∧
      r2 ≠ .error ∧ (res = some .timeOut → r2 = .timeOut) := by
  rintro ⟨ev, rel, hpc, nerr, hres⟩
  have clk := relClock rel
  obtain ⟨prog, hlook, ⟨h0, rfl, rfl⟩ | ⟨h0, x, rfl, hbad, e2⟩⟩ := callNoneInlCases ev nerr
  · -- clock zero: both sides time out at once
    refine ⟨0, Nat.zero_le _, .timeOut, { t1 with clock := t1.clock - 1 + 0 }, ?_, by simp, by simp, by simp,
      ?_, by simp, fun _ => rfl⟩
    · rw [evaluate, if_pos (by simp; omega)]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  rw [hpc] at entry
  cases entry
  have rel' : stateRel (StackSemStateOps.decClock s1) { t1 with clock := t1.clock - 1 } :=
    Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRelDecClock rel
  have nx : x ≠ .error := fun h => nerr (by rw [h])
  obtain ⟨ck, bound, t2, h⟩ := stackWork_correct prog (StackSemStateOps.decClock s1) true (some x) s2
    start (Flapjack.Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] [] { t1 with clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [hpc]⟩
  have firstLe : stackWork prog (StackSemStateOps.decClock s1) ≤ entryWork start s1 := by
    simp only [entryWork, hlook]
    rw [e2]
    omega
  rcases x with v | v | k | k | v | _ | f | _
  · -- `Result v`: only `Loc n 0` is allowed, and procedure `n` halts
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, hh⟩ := hres (by simp)
    · simp at hw
    · simp at hf
    simp only [Option.some.injEq, StackSemResult.result.injEq] at hn
    subst hn
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hcover, hw⟩ := h
    have hsub : sptSubspt s1.code s2.code := by
      simpa [StackSemStateOps.decClock] using (Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono _ _ _ _ e2).2
    obtain ⟨t, evh, tffi, -⟩ := hh { s2 with clock := s2.clock + 1 } ⟨hsub, by simp⟩
    obtain ⟨prog2, hlook2, ⟨h0', -⟩ | ⟨-, x2, hx2, -, e3⟩⟩ := callNoneInlCases evh (by simp)
    · simp at h0'
    simp only [Option.some.injEq] at hx2
    subst hx2
    have hdc : StackSemStateOps.decClock { s2 with clock := s2.clock + 1 } = s2 := by
      simp [StackSemStateOps.decClock]
    rw [hdc] at e3
    simp only at hlook2
    obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp (hcover n (by simp [hlook2]))
    obtain ⟨rfl, rel2⟩ := hw w hw'
    obtain ⟨caP2, pc2, instP2, entry2⟩ := relCode rel2 hlook2
    rw [hw'] at entry2
    cases entry2
    obtain ⟨ck', bound2, t3, h3⟩ := stackWork_correct prog2 s2 true (some (.halt (.word 0))) t n
      (Flapjack.Compiler.Backend.StackAlloc.nextLabHOL prog2 2) [] [] t2 ⟨e3, by simp, rel2, caP2, instP2, by simp [hw']⟩
    simp only [haltView, haltWordView, if_true] at h3
    refine ⟨ck + ck', by
      simp only [entryWork, hlook, e2, hlook2]
      omega, .halt .success, t3, ?_, by simp, by simp, fun _ _ => rfl, ?_, by simp,
      by simp⟩
    · have r1 := run ck'
      rw [show t1.clock - 1 + (ck + ck') = t1.clock - 1 + ck + ck' by omega, r1]
      exact h3.1
    · rw [h3.2, tffi]
  · -- `Exception`: excluded by the hypothesis
    rcases hres (by simp) with ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩
    · simp at hw
    · simp at hf
    · simp at hn
  · simp [StackSemControl.badFunReturn] at hbad
  · simp [StackSemControl.badFunReturn] at hbad
  · -- `Halt v`
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩ := hres (by simp)
    · simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw
      subst hw
      simp only [haltView] at h
      refine ⟨ck, bound.trans firstLe, haltWordView (.word w), t2, h.1, by simp, ?_, by simp, h.2, ?_, by simp⟩
      · intro w' hw'
        simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw'
        subst hw'
        rfl
      · simp only [haltWordView]; split <;> simp
    · simp at hf
    · simp at hn
  · -- `TimeOut`
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hffi, hclk⟩ := h
    refine ⟨ck, bound.trans firstLe, .timeOut, { t2 with clock := t2.clock + 0 }, ?_, by simp, by simp, by simp,
      hffi, by simp, fun _ => rfl⟩
    have r0 := run 0
    simp only [Nat.add_zero] at r0 ⊢
    rw [r0, evaluate, if_pos (by simp [hclk])]
  · -- `FinalFFI f`
    simp only [haltView] at h
    exact ⟨ck, bound.trans firstLe, _, t2, h.1, fun f' hf' => by cases hf'; rfl, by simp, by simp, h.2, by simp, by simp⟩
  · exact (nx rfl).elim


#print axioms flattenEntry_bounded
end InitECandidate.Runtime.StackToLab
