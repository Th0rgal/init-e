import InitECandidate.Runtime.SourceCostLoopLiveGeometryG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- Every actual argument read is included in the compiler-computed footprint. -/
theorem live_argument_memberG (key : Nat) (arguments : List Nat) (member : key ∈ arguments) :
    sptMem key (sptFromAList (arguments.map fun x => (x, ()))) := by
  induction arguments with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.map_cons, sptFromAList, sptMem_sptInsert]
    rcases List.mem_cons.mp member with rfl | rest
    · exact Or.inl rfl
    · exact Or.inr (ih rest)

/-- Successful argument evaluation is preserved by its actual live projection. -/
theorem live_argument_valuesG {F : Type} (s : LoopSemStateFiniteExact 64 F)
    (locals : Spt (WordLocW 64)) (arguments : List Nat) (live : NumSet)
    (input : sptSubspt (sptInter s.locals
      (sptUnion (sptFromAList (arguments.map fun x => (x, ()))) live)) locals)
    {values : List (WordLocW 64)} (run : getVars arguments s = some values) :
    getVars arguments { s with locals := locals } = some values := by
  have reads : ∀ key value, key ∈ arguments → sptLookup key s.locals = some value →
      sptLookup key locals = some value := by
    intro key value member read
    exact live_projection_lookupG input
      ((sptMem_sptUnion _ _ key).mpr (Or.inl (live_argument_memberG key arguments member))) read
  clear input
  induction arguments generalizing values with
  | nil => exact run
  | cons head tail ih =>
    rw [getVars_cons] at run ⊢
    cases read : sptLookup head s.locals with
    | none => simp only [read, Option.bind_none, reduceCtorEq] at run
    | some value =>
      rw [reads head value (by simp) read]
      simp only [read, Option.bind_some] at run ⊢
      cases rest : getVars tail s with
      | none => simp only [rest, Option.map_none, reduceCtorEq] at run
      | some vs =>
        have target := ih rest (fun key value member read => reads key value (by simp [member]) read)
        rw [target]
        simpa only [rest] using run

/-- Tail-call callees are unchanged by liveness pruning and start in the SAME
state after the argument environment replaces caller locals. Their work is
reused exactly, not multiplied by a recursive optimizer coefficient. -/
theorem loop_live_paid_call_tailG {F : Type}
    {s post : LoopSemStateFiniteExact 64 F} {target : Option Nat} {arguments : List Nat}
    {handler : Option (Nat × HolLoopProg 64 × HolLoopProg 64 × NumSet)}
    {values : List (WordLocW 64)} {env : Spt (WordLocW 64)} {prog : HolLoopProg 64}
    {result : Option (LoopResultExact 64)} {wb : Nat}
    (args : getVars arguments s = some values)
    (find : findCode target values s.code = some (env, prog))
    (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
    (body : LoopWorkG L { decClock s with locals := env } prog (result, post) wb)
    (nonerror : (loopTailExit result post).1 ≠ some .error) :
    LoopLivePaidG L s (.call none target arguments handler) (loopTailExit result post)
      (189 + 39 * arguments.length + wb) := by
  cases handler with
  | some value => simp at noHandler
  | none =>
    intro contexts locals live input
    have input' : sptSubspt (sptInter s.locals
        (sptUnion (sptFromAList (arguments.map fun x => (x, ()))) live)) locals := by
      simpa only [shrinkHOL] using input
    have targetArgs := live_argument_valuesG s locals arguments live input' args
    have targetBody : LoopWorkG L { decClock { s with locals := locals } with locals := env }
        prog (result, post) wb := by simpa only [decClock] using body
    have targetRun := LoopWorkG.callTail (handler := none) targetArgs find rfl clock targetBody
    have target' : LoopWorkG L { s with locals := locals }
        (shrinkHOL contexts (.call none target arguments none) live).1
        (loopTailExit result post) (189 + 39 * arguments.length + wb) := by
      simpa only [shrinkHOL] using targetRun
    exact loop_live_finishG (LoopWorkG.callTail args find rfl clock body) nonerror
      contexts locals live input target' (Nat.le_refl _)

/-- Returning calls cut a subset of the original saved caller footprint. -/
theorem live_return_cut_insideG (names : List Nat) (wanted live : NumSet) (key : Nat)
    (member : sptMem key (sptListDelete names (sptInter wanted live))) :
    sptMem key live := by
  have retained : sptMem key (sptInter wanted live) := by
    by_cases removed : key ∈ names
    · simp only [sptMem, sptDomain, sptLookup_sptListDelete, if_pos removed,
        Option.isSome_none, Bool.false_eq_true] at member
    · simpa only [sptMem, sptDomain, sptLookup_sptListDelete, if_neg removed] using member
  exact ((live_mem_interG wanted live key).mp retained).2

/-- Calls without handlers preserve the callee trace exactly; only the saved
caller locals are pruned. Return copies keep their original size charge. -/
theorem loop_live_paid_call_ret_plainG {F : Type}
    {s entry post : LoopSemStateFiniteExact 64 F} {names : List Nat} {live : NumSet}
    {target : Option Nat} {arguments : List Nat} {values : List (WordLocW 64)}
    {env : Spt (WordLocW 64)} {prog : HolLoopProg 64}
    {result : Option (LoopResultExact 64)} {wb : Nat}
    (args : getVars arguments s = some values)
    (find : findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : cutRes live (none, s) = (none, entry))
    (body : LoopWorkG L { entry with locals := env } prog (result, post) wb)
    (nonerror : (loopRetExit result post entry names).1 ≠ some .error) :
    LoopLivePaidG L s (.call (some (names, live)) target arguments none)
      (loopRetExit result post entry names) (189 + 39 * arguments.length + wb + 49 * loopRetWords result) := by
  intro contexts locals wanted input
  let saved := sptListDelete names (sptInter wanted live)
  have input' : sptSubspt (sptInter s.locals
      (sptUnion (sptFromAList (arguments.map fun x => (x, ()))) saved)) locals := by
    simpa only [shrinkHOL] using input
  have targetArgs := live_argument_valuesG s locals arguments saved input' args
  have savedInput : sptSubspt (sptInter s.locals saved) locals :=
    live_projection_weakenG input' (fun key member => (sptMem_sptUnion _ _ key).mpr (Or.inr member))
  obtain ⟨entryLocals, targetCut, _⟩ := live_projection_cutG s locals live saved .ln savedInput
    (live_return_cut_insideG names wanted live)
    (by intro key impossible; simp [sptMem, sptDomain, sptLookup] at impossible)
    (by rw [cut]; simp)
  rw [cut] at targetCut
  have targetBody : LoopWorkG L { { entry with locals := entryLocals } with locals := env }
      prog (result, post) wb := body
  have plain : loopRetPlain result names none := by
    cases result with
    | none => trivial
    | some r => cases r <;> trivial
  have targetRun := LoopWorkG.callRet (handler := none) targetArgs find nodup targetCut targetBody plain
  have target' : LoopWorkG L { s with locals := locals }
      (shrinkHOL contexts (.call (some (names, live)) target arguments none) wanted).1
      (loopRetExit result post { entry with locals := entryLocals } names)
      (189 + 39 * arguments.length + wb + 49 * loopRetWords result) := by
    simpa only [shrinkHOL, saved] using targetRun
  exact loop_live_finishG (LoopWorkG.callRet args find nodup cut body plain) nonerror
    contexts locals wanted input target' (Nat.le_refl _)

#print axioms loop_live_paid_call_ret_plainG
#print axioms live_argument_valuesG
#print axioms loop_live_paid_call_tailG
end InitECandidate.Runtime.FineCost
