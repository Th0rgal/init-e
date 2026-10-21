import InitECandidate.Runtime.WordColourIndexedLoop
import InitECandidate.Runtime.WordColourCostCall

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)
set_option maxHeartbeats 10000000

/-- The allocated function table: every source entry keeps its label and
arity, and its body is coloured by that label's colouring. -/
def ColourAllocTable (source target : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (col : Nat → Nat → Nat) : Prop :=
  ∀ label, (sptLookup label source = none → sptLookup label target = none) ∧
    ∀ arity body, sptLookup label source = some (arity, body) →
      sptLookup label target = some (arity, applyColour (col label) body)

/-- Lookup through the allocated table finds the callee coloured by its own
resolved label, for direct and indirect calls alike. -/
theorem ColourAllocTable.findCode {source target : Spt (Nat × WordLangProgHOL (BitVec 64))}
    {col : Nat → Nat → Nat} (table : ColourAllocTable source target col)
    (destination : Option Nat) (arguments : List (WordLocW 64)) (sizes : Spt Nat) :
    (wordSemFindCode destination arguments source sizes = none →
      wordSemFindCode destination arguments target sizes = none) ∧
    ∀ args body size, wordSemFindCode destination arguments source sizes = some (args, body, size) →
      wordSemFindCode destination arguments target sizes =
        some (args, applyColour (col ((wordCallLabel destination arguments).getD 0)) body, size) := by
  have lookupCases : ∀ label, (sptLookup label source = none ∧ sptLookup label target = none) ∨
      ∃ arity body, sptLookup label source = some (arity, body) ∧
        sptLookup label target = some (arity, applyColour (col label) body) := by
    intro label
    rcases found : sptLookup label source with _ | ⟨arity, body⟩
    · exact Or.inl ⟨rfl, (table label).1 found⟩
    · exact Or.inr ⟨arity, body, rfl, (table label).2 arity body found⟩
  cases destination with
  | some label =>
    simp only [wordSemFindCode, wordCallLabel, Option.getD_some]
    rcases lookupCases label with (⟨none1, none2⟩ | ⟨arity, body, found, lookup⟩)
    · rw [none1, none2]
      exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
    · rw [found, lookup]
      dsimp only
      split
      · refine ⟨(fun h => by cases h), ?_⟩
        intro args body' size h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | none =>
    simp only [wordSemFindCode, wordCallLabel]
    split
    · exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
    · rename_i nonempty
      try simp only [nonempty, dite_false]
      split
      · rename_i label pointer
        simp only [pointer, Option.getD_some]
        rcases lookupCases label with (⟨none1, none2⟩ | ⟨arity, body, found, lookup⟩)
        · rw [none1, none2]
          exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
        · rw [found, lookup]
          dsimp only
          split
          · refine ⟨(fun h => by cases h), ?_⟩
            intro args body' size h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            rfl
          · exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
      · exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩

/-- Related caller states give callee entries that differ only in code and
scheduler. -/
theorem callEnv_decClock_codeFrame {C F : Type} {st cst : WordSemStateFiniteExact 64 C F}
    (hs : wordStateEqRel st {cst with code := st.code})
    (arguments : List (WordLocW 64)) (size : Option Nat) :
    callEnv arguments size (decClock cst) =
      {callEnv arguments size (decClock st) with code := cst.code, permute := cst.permute} := by
  have eq := wsrEq hs
  have restore : cst = {({st with permute := cst.permute, locals := cst.locals} :
      WordSemStateFiniteExact 64 C F) with code := cst.code} := by
    rw [eq]
  rw [restore]
  rfl

theorem evenStartingLocals_callEnv {C F : Type} (arguments : List (WordLocW 64)) (size : Option Nat)
    (state : WordSemStateFiniteExact 64 C F) :
    evenStartingLocals (callEnv arguments size state).locals := by
  intro key member
  obtain ⟨half, rfl⟩ := sptEvenFromList2 arguments key member
  simp only [isPhyVar, decide_eq_true_eq]
  omega

/-- Terminal callee locals are equal under the callee's own colouring post. -/
theorem applyColourLocals_terminal (g : Nat → Nat) (result : WordSemResult 64)
    (sourceLocals targetLocals : Spt (WordLocW 64))
    (terminal : wordSemBadFunReturn (some result) = false)
    (locals : applyColourLocals g .ln [] (some result) sourceLocals targetLocals) :
    sourceLocals = targetLocals := by
  cases result <;> simp_all [wordSemBadFunReturn, applyColourLocals]

/-- Tail calls through the allocated table. -/
theorem colourIndexed_tail {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (function : Nat) (f : Nat → Nat) (table : ColourAllocTable source target col)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    ColourIndexedGoal C F TP SP source target col function f (.call none dest args handler) := by
  classical
  rintro st cst live lt calleeIH free sourceCode targetCode ⟨hok, hs, hr⟩
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have stuck : (evaluate (.call none dest args handler) st).1 = some .error →
      ColourIndexedPost TP SP function f (.call none dest args handler) live lt st cst :=
    fun stop => ⟨st.permute, Or.inl stop⟩
  have hargs : ∀ a, a ∈ args → sptDomain (getLive (.call none dest args handler) live lt) a := by
    intro a ha
    simp only [getLive]; exact (sptDomain_numsetIns _ _ _).mpr (Or.inr ha)
  cases hgv : getVars args st with
  | none => exact stuck (by rw [ht, hgv])
  | some xv =>
  have hgvC : getVars (args.map f) cst = some xv :=
    strongLocalsRelGetVars args xv f _ st cst ⟨hr, hargs, hgv⟩
  have hbadC : wordSemBadDestArgs dest (args.map f) = wordSemBadDestArgs dest args := by
    simp [wordSemBadDestArgs]
  by_cases hbad : wordSemBadDestArgs dest args = true
  · exact stuck (by rw [ht, hgv]; dsimp only; rw [if_pos hbad])
  have hbadF : wordSemBadDestArgs dest args = false := by simpa using hbad
  have hbadC' : wordSemBadDestArgs dest (args.map f) = false := by rw [hbadC]; exact hbadF
  have hss : cst.stackSize = st.stackSize := by unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.1
  have hclk : cst.clock = st.clock := by unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases handler with
  | some hv => exact stuck (by rw [ht, hgv]; dsimp only; rw [if_neg hbad]; split <;> rfl)
  | none =>
  cases hfc : wordSemFindCode dest xv st.code st.stackSize with
  | none => exact stuck (by rw [ht, hgv]; dsimp only; rw [if_neg hbad]; simp only [wordSemAddRetLoc, hfc])
  | some found =>
  obtain ⟨args1, body, size⟩ := found
  have sourceFound : wordSemFindCode dest xv source st.stackSize = some (args1, body, size) := by
    rw [← sourceCode]; exact hfc
  let g := (wordCallLabel dest xv).getD 0
  have hfcC : wordSemFindCode dest xv cst.code cst.stackSize =
      some (args1, applyColour (col g) body, size) := by
    rw [targetCode, hss]
    exact (table.findCode dest xv st.stackSize).2 args1 body size sourceFound
  obtain ⟨label, labelEq, lookup⟩ := wordCallLabel_findCode dest xv args1 source st.stackSize body size sourceFound
  have gEq : g = label := by simp only [g, labelEq, Option.getD_some]
  have targetCall : applyColour f (.call none dest args none : WordLangProgHOL (BitVec 64)) =
      .call none dest (args.map f) none := by
    rw [applyColour.eq_def]
  have head := leafPrice (.call none dest args none)
  rw [targetCall] at head
  by_cases hz : st.clock = 0
  · -- both calls time out before entering the callee
    refine ⟨st.permute, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · show (evaluate _ st).1 = _
      rw [targetCall, ht st, ht cst, hgv, hgvC]
      simp only [hbadF, hbadC', Bool.false_eq_true, if_false, wordSemAddRetLoc, hfc, hfcC, hz, hclk,
        if_true]
    · show wordStateEqRel (evaluate _ st).2 _
      rw [targetCall, ht st, ht cst, hgv, hgvC]
      simp only [hbadF, hbadC', Bool.false_eq_true, if_false, wordSemAddRetLoc, hfc, hfcC, hz, hclk,
        if_true]
      simp_all [wordStateEqRel, flushState]
    · show applyColourLocals f live lt (evaluate _ st).1 (evaluate _ st).2.locals _
      rw [targetCall, ht st, ht cst, hgv, hgvC]
      simp only [hbadF, hbadC', Bool.false_eq_true, if_false, wordSemAddRetLoc, hfc, hfcC, hz, hclk,
        if_true]
      simp [applyColourLocals, flushState]
    · rw [targetCall, tail_call_cost_timeout _ dest (args.map f) cst xv hgvC hbadC' args1 _ size hfcC
          (hclk.trans hz)]
      have sourceZero : wordFunctionExecutionCost (fun l p _ => SP l p) function (.call none dest args none)
          {st with permute := st.permute} = SP function (.call none dest args none) := by
        rw [wordFunctionExecutionCost]
        simp only [getVars_withPermute, hgv, hbadF, Bool.false_eq_true, if_false, wordSemAddRetLoc]
        simp only [show ({st with permute := st.permute} : WordSemStateFiniteExact 64 C F).code = st.code from rfl,
          show ({st with permute := st.permute} : WordSemStateFiniteExact 64 C F).stackSize = st.stackSize from rfl,
          hfc, show ({st with permute := st.permute} : WordSemStateFiniteExact 64 C F).clock = st.clock from rfl,
          hz, dite_true]
      rw [sourceZero]
      exact head
  -- the callee runs from entries that differ only in code and scheduler
  let entry := callEnv args1 size (decClock st)
  have targetEntry : callEnv args1 size (decClock cst) =
      {entry with code := target, permute := cst.permute} := by
    rw [callEnv_decClock_codeFrame hs, targetCode]
  have entryCode : entry.code = source := sourceCode
  have smaller : Prod.Lex (· < ·) (· < ·) (entry.termdep, entry.clock) (st.termdep, st.clock) := by
    simp only [entry, WordSemStateFiniteExact.callEnv, decClock]
    apply Prod.Lex.right
    omega
  obtain ⟨p', hp'⟩ := calleeIH label args1.length body entry cst.permute smaller lookup entryCode
    (evenStartingLocals_callEnv args1 size (decClock st))
  rw [← gEq] at hp'
  rw [← targetEntry] at hp'
  dsimp only at hp'
  have sourceEntry : callEnv args1 size (decClock {st with permute := p'}) = {entry with permute := p'} := rfl
  have sourceRun : evaluate (.call none dest args none) {st with permute := p'} =
      match evaluate body {entry with permute := p'} with
      | (r, s') => if wordSemBadFunReturn r then (some .error, s') else (r, s') := by
    rw [ht, getVars_withPermute, hgv]
    dsimp only
    rw [if_neg hbad]
    simp only [wordSemAddRetLoc, show ({st with permute := p'} : WordSemStateFiniteExact 64 C F).code = st.code from rfl,
      show ({st with permute := p'} : WordSemStateFiniteExact 64 C F).stackSize = st.stackSize from rfl, hfc,
      show ({st with permute := p'} : WordSemStateFiniteExact 64 C F).clock = st.clock from rfl, hz, if_false]
    rw [sourceEntry]
  have targetRun : evaluate (applyColour f (.call none dest args none)) cst =
      match evaluate (applyColour (col g) body) (callEnv args1 size (decClock cst)) with
      | (r, s') => if wordSemBadFunReturn r then (some .error, s') else (r, s') := by
    rw [targetCall, ht, hgvC]
    dsimp only
    rw [if_neg (by rw [hbadC]; exact hbad)]
    simp only [wordSemAddRetLoc, hfcC, hclk, hz, if_false]
  refine ⟨p', ?_⟩
  dsimp only
  rw [sourceRun, targetRun]
  rcases calleeSource : evaluate body {entry with permute := p'} with ⟨r, s'⟩
  rcases calleeTarget : evaluate (applyColour (col g) body) (callEnv args1 size (decClock cst)) with ⟨r', t'⟩
  rw [calleeSource, calleeTarget] at hp'
  dsimp only at hp' ⊢
  have sourceCost : wordFunctionExecutionCost (fun l p _ => SP l p) function (.call none dest args none)
      {st with permute := p'} = SP function (.call none dest args none) +
        wordFunctionExecutionCost (fun l p _ => SP l p) g body {entry with permute := p'} := by
    rw [function_tail_call_cost _ function dest args {st with permute := p'} xv
      (by rw [getVars_withPermute]; exact hgv) hbadF args1 body size hfc hz, sourceEntry]
  have targetCost : wordExecutionCost (fun p _ => TP p) (applyColour f (.call none dest args none)) cst =
      TP (.call none dest (args.map f) none) +
        wordExecutionCost (fun p _ => TP p) (applyColour (col g) body) (callEnv args1 size (decClock cst)) := by
    rw [targetCall]
    exact tail_call_cost _ dest (args.map f) cst xv hgvC hbadC' args1 _ size hfcC (by rw [hclk]; exact hz)
  rw [sourceCost, targetCost]
  rcases hp' with bad | ⟨same, frame, locals, cost⟩
  · left
    subst bad
    simp [wordSemBadFunReturn]
  subst r'
  by_cases badReturn : wordSemBadFunReturn r = true
  · left
    simp [badReturn]
  have good : wordSemBadFunReturn r = false := by simpa using badReturn
  right
  simp only [good, Bool.false_eq_true, if_false]
  refine ⟨by trivial, frame, ?_, Nat.add_le_add head cost⟩
  rcases r with _ | result
  · simp [wordSemBadFunReturn] at good
  have equal := applyColourLocals_terminal (col g) result s'.locals t'.locals good locals
  cases result <;> simp_all [wordSemBadFunReturn, applyColourLocals]

#print axioms ColourAllocTable.findCode
#print axioms callEnv_decClock_codeFrame
#print axioms colourIndexed_tail
end InitECandidate.Runtime.FineCost
