import InitECandidate.Runtime.SourceCostLoopLiveCallExit
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- With no remaining clock a call cannot reach a callee body, independently
of whether argument lookup or frame validation fails earlier. -/
theorem loop_call_short_zero {F : Type} (s : LoopSemStateFiniteExact 64 F)
    (returns : Option (List Nat × NumSet)) (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet))
    (zero : s.clock = 0) : loopCallShort s returns target arguments handler := by
  unfold loopCallShort
  cases args : getVars arguments s with
  | none => exact Or.inl rfl
  | some values =>
    refine Or.inr ⟨values, rfl, ?_⟩
    cases found : findCode target values s.code with
    | none => exact Or.inl rfl
    | some pair =>
      rcases pair with ⟨env, prog⟩
      refine Or.inr ⟨env, prog, rfl, ?_⟩
      cases returns with
      | none => exact Or.inl ⟨rfl, Or.inr zero⟩
      | some pair =>
        rcases pair with ⟨names, live⟩
        refine Or.inr ⟨names, live, rfl, ?_⟩
        by_cases nodup : names.Nodup
        · right
          cases cut : cutState live s with
          | none => exact ⟨.error, s, by simp only [cutRes, cut]⟩
          | some state => exact ⟨.timeOut, { state with locals := .ln }, by
              simp only [cutRes, cut, cutState_some_clock cut, zero, ↓reduceIte]⟩
        · exact Or.inl nodup

/-- A non-error early call exit must be its clock-zero timeout. Malformed
arguments, unknown callees and invalid frames are errors, not cheap successes. -/
theorem loop_call_short_nonerror_zero {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {returns : Option (List Nat × NumSet)} {target : Option Nat} {arguments : List Nat}
    {handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)} {output}
    (short : loopCallShort s returns target arguments handler)
    (run : evaluate (.call returns target arguments handler) s = output)
    (nonerror : output.1 ≠ some .error) : s.clock = 0 := by
  have ne : (evaluate (.call returns target arguments handler) s).1 ≠ some .error := by
    simpa only [run] using nonerror
  rcases short with failed | ⟨values, args, stopped⟩
  · simp only [evaluate, failed] at ne
    exact False.elim (ne rfl)
  · rcases stopped with missing | ⟨env, prog, found, stopped⟩
    · simp only [evaluate, args, missing] at ne
      exact False.elim (ne rfl)
    · rcases stopped with ⟨rfl, badHandler | zero⟩ | ⟨names, live, rfl, invalid | stopped⟩
      · simp only [evaluate, args, found, badHandler, ↓reduceIte] at ne
        exact False.elim (ne rfl)
      · exact zero
      · simp only [evaluate, args, found, invalid, ↓reduceIte] at ne
        exact False.elim (ne rfl)
      · obtain ⟨result, post, stopped⟩ := stopped
        by_cases nodup : names.Nodup
        · simp only [evaluate, args, found, nodup, not_true_eq_false, ↓reduceIte] at ne
          rw [stopped] at ne
          dsimp only at ne
          apply Classical.byContradiction
          intro positive
          cases cut : cutState live s with
          | none =>
            have error : result = .error := by simpa only [cutRes, cut, Prod.mk.injEq, Option.some.injEq] using (congrArg Prod.fst stopped).symm
            exact ne (by rw [error])
          | some state => simp only [cutRes, cut, cutState_some_clock cut, positive, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, false_and] at stopped
        · simp only [evaluate, args, found, nodup, not_false_eq_true, ↓reduceIte] at ne
          exact False.elim (ne rfl)

/-- Shrink preserves a call entry and its argument count. At clock zero the
costed target trace follows its actual early-exit evaluation without a callee. -/
theorem loop_live_zero_call_work {F : Type} (s : LoopSemStateFiniteExact 64 F)
    (returns : Option (List Nat × NumSet)) (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet))
    (contexts : List (NumSet × NumSet)) (live : NumSet) (output)
    (zero : s.clock = 0)
    (evaluated : evaluate (shrinkHOL contexts (.call returns target arguments handler) live).1 s = output) :
    LoopWork s (shrinkHOL contexts (.call returns target arguments handler) live).1
      output (1 + arguments.length) := by
  cases returns with
  | none =>
    simp only [shrinkHOL] at evaluated ⊢
    exact LoopWork.callShort (loop_call_short_zero s _ _ _ _ zero) evaluated
  | some pair =>
    rcases pair with ⟨names, saved⟩
    cases handler with
    | none =>
      simp only [shrinkHOL] at evaluated ⊢
      exact LoopWork.callShort (loop_call_short_zero s _ _ _ _ zero) evaluated
    | some pair =>
      rcases pair with ⟨exceptionName, handlerProgram, continuation, liveOut⟩
      rcases contCompiled : shrinkHOL contexts continuation live with ⟨contCode, contLive⟩
      rcases handlerCompiled : shrinkHOL contexts handlerProgram live with ⟨handlerCode, handlerLive⟩
      simp only [shrinkHOL, contCompiled, handlerCompiled] at evaluated ⊢
      exact LoopWork.callShort (loop_call_short_zero s _ _ _ _ zero) evaluated

/-- The last early-call case preserves its entry/argument charge exactly. -/
theorem loop_live_paid_call_short {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {returns : Option (List Nat × NumSet)} {target : Option Nat} {arguments : List Nat}
    {handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)} {result}
    (short : loopCallShort s returns target arguments handler)
    (run : evaluate (.call returns target arguments handler) s = (result, post))
    (nonerror : result ≠ some .error) :
    LoopLivePaid s (.call returns target arguments handler) (result, post) (1 + arguments.length) := by
  have zero := loop_call_short_nonerror_zero short run nonerror
  intro contexts locals live input
  obtain ⟨targetLocals, evaluated, related⟩ := loopLive_compile_correct
    (.call returns target arguments handler) s result post contexts locals
    (shrinkHOL contexts (.call returns target arguments handler) live).1
    (shrinkHOL contexts (.call returns target arguments handler) live).2 live
    ⟨run, nonerror, rfl, input⟩
  refine ⟨targetLocals, 1 + arguments.length,
    loop_live_zero_call_work { s with locals := locals } returns target arguments handler
      contexts live _ zero evaluated, Nat.le_refl _, ?_⟩
  cases result with
  | none => exact related
  | some r => cases r <;> exact related

#print axioms loop_live_paid_call_short
#print axioms loop_call_short_zero
#print axioms loop_call_short_nonerror_zero
end InitECandidate.Runtime.FineCost
