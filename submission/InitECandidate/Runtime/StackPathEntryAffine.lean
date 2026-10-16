import InitECandidate.Runtime.StackPathEntryBudget
import InitECandidate.Runtime.StackPathAffine

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

/-- An entry body and its actual final halt share one affine fuel budget.
The final procedure receives only the clock left by the entry body. -/
theorem pathEntryWork_affine_body {width : Nat} [NeZero width] {C F : Type}
    (limit start : Nat) (s post : StackSemStateFiniteExact width C F)
    (prog : HolProg width) (result : Option (StackSemResult width))
    (bounded : CodeSizeState limit s)
    (lookup : sptLookup start s.code = some prog)
    (run : StackSemEvaluate.evaluate (prog, decClock s) = (result, post))
    (notError : result ≠ some .error)
    (halts : ∀ n, result = some (.result (.loc n 0)) →
      ∀ body, sptLookup n post.code = some body →
        ∃ final, StackSemEvaluate.evaluate (body, post) = (some (.halt (.word 0)), final)) :
    pathEntryWork start s ≤ (2 * limit + 2) * s.clock + 4 * limit := by
  have small := bounded.code start prog lookup
  have first := pathWork_affine limit prog (decClock s) small bounded.decClock result post run notError
  have lower := StackSemEvaluateClock.evaluateClock prog (decClock s) result post run
  have postBound := CodeSizeState.of_evaluate run bounded.decClock
  have last : (match (generalizing := false) result with
      | some (.result (.loc n 0)) =>
          match sptLookup n post.code with
          | none => 0
          | some body => pathWork body post
      | _ => 0) ≤ (2 * limit + 2) * post.clock + 2 * limit := by
    split
    · rename_i ignored n
      split
      · omega
      · rename_i body found
        obtain ⟨final, halted⟩ := halts n rfl body found
        exact pathWork_affine_fuel limit body post (postBound.code n body found)
          postBound _ final halted (by simp)
    · omega
  have fuel : ((decClock s).clock - post.clock) + post.clock ≤ s.clock := by
    simp only [StackSemStateOps.decClock] at lower ⊢
    omega
  have scaled := Nat.mul_le_mul_left (2 * limit + 2) fuel
  have potential := Nat.mul_le_mul_left 2 small
  simp only [Nat.mul_add] at scaled
  simp only [pathEntryWork, lookup, run]
  change pathWork prog (decClock s) + _ ≤ _
  exact Nat.le_trans (Nat.add_le_add first last) (by omega)

/-- The original entry theorem's semantic halt premise supplies the actual
final body execution required by the affine budget, even with no clock left. -/
theorem pathEntryWork_affine_return {width : Nat} [NeZero width] {C F : Type}
    (limit start n : Nat) (s post : StackSemStateFiniteExact width C F)
    (prog : HolProg width) (bounded : CodeSizeState limit s)
    (lookup : sptLookup start s.code = some prog)
    (run : StackSemEvaluate.evaluate (prog, decClock s) = (some (.result (.loc n 0)), post))
    (halts : ∀ next : StackSemStateFiniteExact width C F,
      sptSubspt s.code next.code ∧ next.clock ≠ 0 →
      ∃ final, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), next) =
        (some (.halt (.word 0)), final) ∧ final.ffi = next.ffi ∧ final.clock = next.clock - 1) :
    pathEntryWork start s ≤ (2 * limit + 2) * s.clock + 4 * limit := by
  apply pathEntryWork_affine_body limit start s post prog _ bounded lookup run (by simp)
  intro label same body found
  simp only [Option.some.injEq, StackSemResult.result.injEq, WordLocW.loc.injEq] at same
  obtain ⟨rfl, _⟩ := same
  have sub : sptSubspt s.code post.code := by
    simpa [StackSemStateOps.decClock] using
      (Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono _ _ _ _ run).2
  obtain ⟨final, halted, _, _⟩ := halts {post with clock := post.clock + 1} ⟨sub, by simp⟩
  obtain ⟨actual, actualLookup, ⟨zero, _⟩ | ⟨_, outcome, sameOutcome, _, bodyRun⟩⟩ :=
    callNoneInlCases halted (by simp)
  · simp at zero
  have identical : actual = body := by
    simp only at actualLookup
    rw [found] at actualLookup
    exact Option.some.inj actualLookup.symm
  subst actual
  simp only [Option.some.injEq] at sameOutcome
  subst sameOutcome
  exact ⟨final, by simpa [StackSemStateOps.decClock] using bodyRun⟩

/- The full entry simulation retains all original outcome and FFI guarantees. -/
theorem flattenEntry_affine_bounded {width : Nat} [NeZero width] {C F : Type} {start : Nat}
    {s1 s2 : StackSemStateFiniteExact width C F} {res : Option (StackSemResult width)}
    (limit : Nat) (bounded : CodeSizeState limit s1)
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
    ∃ (ck : Nat), ck ≤ (2 * limit + 2) * s1.clock + 4 * limit ∧ ∃ (r2 : MachineResult) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
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
  have original := flattenEntry_path_bounded ⟨ev, rel, hpc, nerr, hres⟩
  have clk := relClock rel
  obtain ⟨prog, found, ⟨zero, rfl, rfl⟩ | ⟨positive, outcome, rfl, _, bodyRun⟩⟩ := callNoneInlCases ev nerr
  · refine ⟨0, Nat.zero_le _, .timeOut, {t1 with clock := t1.clock - 1 + 0}, ?_,
      by simp, by simp, by simp, ?_, by simp, fun _ => rfl⟩
    · rw [evaluate, if_pos (by simp; omega)]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  have bound : pathEntryWork start s1 ≤ (2 * limit + 2) * s1.clock + 4 * limit := by
    apply pathEntryWork_affine_body limit start s1 s2 prog (some outcome) bounded found bodyRun nerr
    intro label same body haltLookup
    obtain ⟨w, impossible⟩ | ⟨f, impossible⟩ | ⟨n, returned, halts⟩ := hres (by rw [same]; simp)
    · rw [same] at impossible
      cases impossible
    · rw [same] at impossible
      cases impossible
    rw [same] at returned
    simp only [Option.some.injEq, StackSemResult.result.injEq, WordLocW.loc.injEq] at returned
    obtain ⟨rfl, _⟩ := returned
    have sub : sptSubspt s1.code s2.code := by
      simpa [StackSemStateOps.decClock] using
        (Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono _ _ _ _ bodyRun).2
    obtain ⟨final, halted, _, _⟩ := halts {s2 with clock := s2.clock + 1} ⟨sub, by simp⟩
    obtain ⟨actual, actualLookup, ⟨zero, _⟩ | ⟨_, result, sameResult, _, haltRun⟩⟩ :=
      callNoneInlCases halted (by simp)
    · simp at zero
    have identical : actual = body := by
      simp only at actualLookup
      rw [haltLookup] at actualLookup
      exact Option.some.inj actualLookup.symm
    subst actual
    simp only [Option.some.injEq] at sameResult
    subst sameResult
    exact ⟨final, by simpa [StackSemStateOps.decClock] using haltRun⟩
  obtain ⟨clock, small, rest⟩ := original
  exact ⟨clock, Nat.le_trans small bound, rest⟩

#print axioms flattenEntry_affine_bounded
#print axioms pathEntryWork_affine_return
#print axioms pathEntryWork_affine_body
end InitECandidate.Runtime.StackToLab
