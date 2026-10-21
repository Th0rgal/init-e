import InitECandidate.Runtime.SSALoopBodyEntry
import InitECandidate.Runtime.SSAQuantitativeAllowanceCore

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Instantiate the quantitative body IH at the actual loop cut and
intersected refreshed map, deriving all six original SSA entry obligations. -/
theorem ssa_loop_allowance_entry {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (entry : Spt Nat → Nat → Nat)
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (sourceEnv : Spt (WordLocW 64))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source.locals target.locals)
    (valid : ssaMapOK next ssa) (allocated : isAllocVar next)
    (vars : everyVarHOL (fun key => decide (key < next)) body = true)
    (entryInjection : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup ssa x = optionLookup ssa y → x = y)
    (exitInjection : ∀ x y, sptDomain exits x → sptDomain exits y →
      optionLookup ssa x = optionLookup ssa y → x = y)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (bounded : ∀ key, sptDomain names key → key < next)
    (tableValid : ltOK tables)
    (bodyIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
      (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) body = true ∧
      ssaMapOK next ssa ∧ ltOK tables → SSAQuantitativeAllowance SP TP body source target ssa next tables (entry ssa next))
    (cut : wordSemCutEnv (names,.ln) source.locals = some sourceEnv) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names,.ln)
        target.locals = some targetEnv ∧
      sptDomain sourceEnv = sptDomain names ∧
      SSAQuantitativeAllowance SP TP body {source with locals := sourceEnv} {target with locals := targetEnv}
        (sptInter ssa names) next ((ssa,names,exits)::tables) (entry (sptInter ssa names) next) := by
  obtain ⟨targetEnv,targetCut,domain,locals⟩ := ssa_loop_entry_cut ssa names next
    source.locals target.locals sourceEnv cut strong entryInjection mapped bounded
  have updatedFrame : Flapjack.WordAlloc.wordStateEqRel
      {source with locals := sourceEnv} {target with locals := targetEnv} := by
    simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame
  have updatedTables : ltOK ((ssa,names,exits)::tables) := by
    intro table member
    rcases List.mem_cons.mp member with equal | member
    · subst table
      exact ⟨entryInjection,exitInjection⟩
    · exact tableValid table member
  exact ⟨targetEnv,targetCut,domain,
    bodyIH _ _ _ _ _ ⟨updatedFrame,locals,allocated,vars,
      ssaMapOKInter next ssa names valid,updatedTables⟩⟩


theorem ssa_loop_recursive_images {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (source target env : Spt α)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source target)
    (cut : wordSemCutEnv (names,.ln) source = some env) :
    ∀ key, sptDomain names key → sptDomain target (optionLookup ssa key) := by
  have subset : ∀ key, sptDomain names key → sptDomain source key := by
    cases cuts : wordSemCutEnvs (names,.ln) source with
    | none => simp [wordSemCutEnv,cuts] at cut
    | some pair => exact (cutEnvsDomainSubset names .ln source pair cuts).1
  intro key inside
  obtain ⟨value,read⟩ := (sptMem_iff_lookup key source).mp (subset key inside)
  exact (sptMem_iff_lookup _ target).mpr ⟨value,strong key value ⟨inside,read⟩⟩


/-- Construct every state-dependent premise of the recursive clock IH from
actual body execution and the successful source re-entry cut. -/
theorem ssa_loop_recursive_entry {C F : Type}
    (refreshed : Spt Nat) (names : Spt Unit)
    (body : WordLangProgHOL (BitVec 64))
    (initial sourcePost targetPost : WordSemStateFiniteExact 64 C F)
    (targetEnv sourceEnv : Spt (WordLocW 64)) (result : Option (WordSemResult 64))
    (run : evaluate body {initial with locals := targetEnv} = (result,targetPost))
    (frame : Flapjack.WordAlloc.wordStateEqRel sourcePost targetPost)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
      (sptDomain names) sourcePost.locals targetPost.locals)
    (cut : wordSemCutEnv (names,.ln) sourcePost.locals = some sourceEnv)
    (nonzero : targetPost.clock ≠ 0) :
    (decClock targetPost).clock < initial.clock ∧
    Flapjack.WordAlloc.wordStateEqRel (decClock sourcePost) (decClock targetPost) ∧
    Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
      (sptDomain names) (decClock sourcePost).locals (decClock targetPost).locals ∧
    (∀ key, sptDomain names key → sptDomain (decClock targetPost).locals
      (optionLookup refreshed key)) := by
  have bound := (evaluate_clock body {initial with locals := targetEnv} result targetPost run).1
  have strict : (decClock targetPost).clock < initial.clock := by
    change targetPost.clock ≤ initial.clock at bound
    simp only [decClock]
    omega
  have nextFrame : Flapjack.WordAlloc.wordStateEqRel (decClock sourcePost) (decClock targetPost) := by
    simp_all only [Flapjack.WordAlloc.wordStateEqRel,decClock,and_true]
  exact ⟨strict,nextFrame,strong,
    ssa_loop_recursive_images refreshed names sourcePost.locals targetPost.locals sourceEnv strong cut⟩

#print axioms ssa_loop_recursive_images
#print axioms ssa_loop_recursive_entry
#print axioms ssa_loop_allowance_entry
end InitECandidate.Runtime.FineCost
