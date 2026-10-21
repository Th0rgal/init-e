import InitECandidate.Runtime.SourceCostLoopWorkG
import Flapjack.Pancake.Proofs.LoopCall.CompileCorrect
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- Repoint a call when its evaluated inputs select exactly the same callee
and environment. Every callee, handler and continuation trace is retained;
only the argument-list charge changes. -/
theorem loop_call_retarget_workG {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {returns : Option (List Nat × NumSet)}
    {target newTarget : Option Nat} {arguments newArguments : List Nat}
    {handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)}
    {output} {w : Nat} (run : LoopWorkG L s (.call returns target arguments handler) output w)
    (previousValues nextValues : List (WordLocW 64))
    (previous : LoopSemStateFiniteExact.getVars arguments s = some previousValues)
    (next : LoopSemStateFiniteExact.getVars newArguments s = some nextValues)
    (same : findCode newTarget nextValues s.code = findCode target previousValues s.code) :
    ∃ w', LoopWorkG L s (.call returns newTarget newArguments handler) output w' ∧
      w' + 39 * arguments.length = w + 39 * newArguments.length := by
  have evaluated : evaluate (.call returns newTarget newArguments handler) s = output := by
    have original := run.sound
    rw [evaluate, previous] at original
    rw [evaluate, next]
    simp only [] at original ⊢
    rw [same]
    exact original
  cases run with
  | atom leaf run => have hd := L.dom _ _ leaf; simp [loopWorkLeafCost] at hd
  | @callShort s returns target arguments handler output short run =>
    have short' : loopCallShort s returns newTarget newArguments handler := by
      unfold loopCallShort at short ⊢
      rcases short with failure | ⟨values, valuesEq, rest⟩
      · rw [previous] at failure; contradiction
      · have matched : values = previousValues := Option.some.inj (valuesEq.symm.trans previous)
        subst matched
        exact Or.inr ⟨nextValues, next, by simpa only [same] using rest⟩
    exact ⟨_, LoopWorkG.callShort short' evaluated, by omega⟩
  | @callTail s target arguments handler values env prog result post wb args find noHandler
      clock body =>
    have matched : values = previousValues := Option.some.inj (args.symm.trans previous)
    have newFind : findCode newTarget nextValues s.code = some (env, prog) := by
      rw [same]; simpa only [matched] using find
    exact ⟨_, LoopWorkG.callTail next newFind noHandler clock body, by omega⟩
  | @callRet s names live target arguments handler values env prog entry result post wb args find
      nodup cut body plain =>
    have matched : values = previousValues := Option.some.inj (args.symm.trans previous)
    have newFind : findCode newTarget nextValues s.code = some (env, prog) := by
      rw [same]; simpa only [matched] using find
    exact ⟨_, LoopWorkG.callRet next newFind nodup cut body plain, by omega⟩
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry returned post wb output wc args find nodup cut body lengths cont =>
    have matched : values = previousValues := Option.some.inj (args.symm.trans previous)
    have newFind : findCode newTarget nextValues s.code = some (env, prog) := by
      rw [same]; simpa only [matched] using find
    exact ⟨_, LoopWorkG.callRetCont next newFind nodup cut body lengths cont, by omega⟩
  | @callHandle s names live target arguments exceptionName handlerProgram continuation liveOut
      values env prog entry exn post wb output wh args find nodup cut body handle =>
    have matched : values = previousValues := Option.some.inj (args.symm.trans previous)
    have newFind : findCode newTarget nextValues s.code = some (env, prog) := by
      rw [same]; simpa only [matched] using find
    exact ⟨_, LoopWorkG.callHandle next newFind nodup cut body handle, by omega⟩

private theorem call_find_frontG (values : List (WordLocW 64)) (target : Nat)
    (code : Spt (List Nat × HolLoopProg 64))
    (last : values.getLast? = some (.loc target 0)) :
    findCode (some target) values.dropLast code = findCode none values code := by
  obtain ⟨head, rest, rfl⟩ : ∃ head rest, values = head :: rest := by
    cases values with
    | nil => simp at last
    | cons head rest => exact ⟨head, rest, rfl⟩
  have actualLast : (head :: rest).getLast (by simp) = .loc target 0 := by
    rw [List.getLast?_eq_some_getLast (by simp)] at last
    exact Option.some.inj last
  simp only [findCode, actualLast]
  cases found : sptLookup target code with
  | none => rfl
  | some definition =>
    rcases definition with ⟨parameters, body⟩
    simp only [List.length_dropLast, List.length_cons, Nat.add_sub_cancel,
      Nat.add_right_cancel_iff]

/-- The actual call-simplification pass preserves a call's executed trace and
can only reduce its charge, using the original known-labels relation. No
callee/handler work bound is assumed: the original traces are reused. -/
theorem loop_call_compiled_workG {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {returns : Option (List Nat × NumSet)}
    {target : Option Nat} {arguments : List Nat}
    {handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)}
    {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w : Nat}
    (run : LoopWorkG L s (.call returns target arguments handler) output w)
    (nonerror : output.1 ≠ some .error) (labels : Spt Nat)
    (known : labelsInHOL labels s.locals) :
    ∃ w', LoopWorkG L s (loopCallCompHOL labels (.call returns target arguments handler)).1
      output w' ∧ w' ≤ w := by
  cases target with
  | some destination =>
    simpa only [loopCallCompHOL] using (show ∃ w',
      LoopWorkG L s (.call returns (some destination) arguments handler) output w' ∧ w' ≤ w from
        ⟨w, run, Nat.le_refl _⟩)
  | none =>
  cases last : arguments.getLast? with
  | none =>
    have empty : arguments = [] := List.getLast?_eq_none_iff.mp last
    subst empty
    apply False.elim
    apply nonerror
    rw [← run.sound]
    simp [evaluate, LoopSemStateFiniteExact.getVars, findCode]
  | some name =>
  cases named : sptLookup name labels with
  | none =>
    simpa only [loopCallCompHOL, last, named] using
      (show ∃ w', LoopWorkG L s (.call returns none arguments handler) output w' ∧ w' ≤ w from
        ⟨w, run, Nat.le_refl _⟩)
  | some destination =>
  have nonempty : arguments ≠ [] := by intro h; subst h; simp at last
  cases values : LoopSemStateFiniteExact.getVars arguments s with
  | none =>
    apply False.elim
    apply nonerror
    rw [← run.sound]
    simp only [evaluate, values]
  | some words =>
  have front := get_vars_front arguments words s ⟨values, nonempty⟩
  have wordLast := get_vars_last arguments words s ⟨values, nonempty⟩
  have nameLast : arguments.getLast nonempty = name := by
    rw [List.getLast?_eq_some_getLast nonempty] at last
    exact Option.some.inj last
  rw [nameLast, known name destination named] at wordLast
  have wordLast' : words.getLast? = some (.loc destination 0) := by
    rw [List.getLast?_eq_some_getLast (getVars_ne_nil values nonempty)]
    exact wordLast.symm
  obtain ⟨w', compiled, cost⟩ := loop_call_retarget_workG
    (newTarget := some destination) (newArguments := arguments.dropLast)
    run words words.dropLast values front (call_find_frontG words destination s.code wordLast')
  refine ⟨w', ?_, ?_⟩
  · simpa only [loopCallCompHOL, last, named] using compiled
  · have shorter : arguments.dropLast.length ≤ arguments.length := by
      simp only [List.length_dropLast]; omega
    omega

#print axioms loop_call_compiled_workG
#print axioms loop_call_retarget_workG
end InitECandidate.Runtime.FineCost
