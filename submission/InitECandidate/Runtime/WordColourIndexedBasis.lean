import InitECandidate.Runtime.WordColourCostBasis
import InitECandidate.Runtime.WordFunctionCostProps
import InitECandidate.Runtime.WordFunctionCallCost
import InitECandidate.Runtime.WordFunctionPermuteGlobalCost
import InitECandidate.Runtime.WordPostSSACodeTable
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-!
# Function-indexed register colouring over allocated function tables

The source runs over the pre-allocation table with per-function prices
`SP function p` (e.g. a ghost price of `p` under that function's actual final
colouring); the target runs over the allocated table with one uniform price
`TP`. Within one function the only price premise is the leaf bound
`TP (applyColour f p) ≤ SP function p` for that function's colouring `f`.
Every callee is reached through the allocated table and is discharged by the
guarded global hypothesis at its own label and colouring.

Source-side scheduler restitching uses the function-indexed permutation cost
transport `FunctionPermuteCostGoal`; the case lemmas take it as a premise
(`IndexedPermuteCost`), discharged by `indexedPermuteCost`.
-/

/-- The indexed permutation transport for every function, program and state. -/
def IndexedPermuteCost (C F : Type) (price : Nat → WordLangProgHOL (BitVec 64) → Nat) : Prop :=
  ∀ (function : Nat) (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F),
    FunctionPermuteCostGoal price function program source

/-- Discharged by the root's whole-program indexed permutation transport. -/
theorem indexedPermuteCost (C F : Type) (price : Nat → WordLangProgHOL (BitVec 64) → Nat) :
    IndexedPermuteCost C F price :=
  fun function program source => word_function_permute_executed_cost price function program source

/-- Predicate form of the indexed stitching, as used at call suffixes. -/
theorem indexed_permute_predicate_cost {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (permuteCost : IndexedPermuteCost C F price) (function : Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (P : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F → Prop)
    (errorP : ∀ post, evaluate program source = (some .error, post) → P (some .error, post))
    (outcome : ∃ permutation, P ((evaluate program source).1,
      {(evaluate program source).2 with permute := permutation})) :
    ∃ permutation, P (evaluate program {source with permute := permutation}) ∧
      wordFunctionExecutionCost (fun l p _ => price l p) function program {source with permute := permutation} =
        wordFunctionExecutionCost (fun l p _ => price l p) function program source := by
  rcases actual : evaluate program source with ⟨result, post⟩
  by_cases error : result = some .error
  · subst result
    exact ⟨source.permute, by simpa only [actual] using errorP post actual, rfl⟩
  · obtain ⟨finalPermutation, predicate⟩ := outcome
    obtain ⟨initialPermutation, run, work⟩ := permuteCost function program source
      finalPermutation (by simpa only [actual] using error)
    refine ⟨initialPermutation, ?_, work⟩
    rw [run]
    exact predicate

/-- One function's quantitative colouring conclusion over the two tables. -/
def ColourIndexedPost {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat) (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec 64)) (live : NumSet) (lt : List (NumSet × NumSet))
    (st cst : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ permutation : Nat → Nat → Nat,
    let sourceState := {st with permute := permutation}
    let sourceRun := evaluate prog sourceState
    let targetRun := evaluate (applyColour f prog) cst
    sourceRun.1 = some .error ∨
      sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 {targetRun.2 with code := sourceRun.2.code} ∧
        applyColourLocals f live lt sourceRun.1 sourceRun.2.locals targetRun.2.locals ∧
        wordExecutionCost (fun p _ => TP p) (applyColour f prog) cst ≤
          wordFunctionExecutionCost (fun l p _ => SP l p) function prog sourceState

/-- `evaluate_apply_colour`'s premises over the two tables. -/
def ColourIndexedGoal (C F : Type) (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (function : Nat) (f : Nat → Nat)
    (prog : WordLangProgHOL (BitVec 64)) : Prop :=
  ∀ (st cst : WordSemStateFiniteExact 64 C F) (live : NumSet) (lt : List (NumSet × NumSet)),
    noInstallSubprogsHOL prog = true → st.code = source → cst.code = target →
    colouringOk f prog live lt ∧ wordStateEqRel st {cst with code := st.code} ∧
      strongLocalsRel f (sptDomain (getLive prog live lt)) st.locals cst.locals →
    ColourIndexedPost TP SP function f prog live lt st cst

/-- The subprogram checker inspects only normalized node shapes, which
colouring never changes. -/
theorem notCreated_applyColour (arb : WordMemOp) (P : WordLangProgHOL (BitVec 64) → Bool)
    (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64)) :
    notCreatedSubprogsWithMemOp arb P (applyColour f p) = notCreatedSubprogsWithMemOp arb P p := by
  cases p
  case seq first second =>
    simp only [applyColour, notCreatedSubprogsWithMemOp, notCreated_applyColour arb P f first,
      notCreated_applyColour arb P f second]
  case ite cmp reg operand first second =>
    simp only [applyColour, notCreatedSubprogsWithMemOp, notCreated_applyColour arb P f first,
      notCreated_applyColour arb P f second]
  case loop names body exits =>
    simp only [applyColour, notCreatedSubprogsWithMemOp, notCreated_applyColour arb P f body]
  case mustTerminate body =>
    simp only [applyColour, notCreatedSubprogsWithMemOp, notCreated_applyColour arb P f body]
  case call returns destination arguments handler =>
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩ <;>
      rcases handler with _ | ⟨reg, code, h1, h2⟩ <;>
      rw [applyColour.eq_def] <;>
      simp only [notCreatedSubprogsWithMemOp]
    · rw [notCreated_applyColour arb P f code]
    · rw [notCreated_applyColour arb P f continuation]
    · rw [notCreated_applyColour arb P f continuation, notCreated_applyColour arb P f code]
  all_goals rfl
termination_by sizeOf p

theorem noInstall_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64))
    (free : noInstallSubprogsHOL p = true) : noInstallSubprogsHOL (applyColour f p) = true := by
  unfold noInstallSubprogsHOL at free ⊢
  rw [notCreated_applyColour]
  exact free

/-- A non-control leaf runs identically over either function table. -/
theorem leaf_code_frame {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (state : WordSemStateFiniteExact 64 C F) (table : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (sameDomain : ∀ label, sptMem label table = sptMem label state.code)
    (leaf : WordToWord.cscLeaf program = true) :
    evaluate program {state with code := table} =
      ((evaluate program state).1, {(evaluate program state).2 with code := table}) := by
  have frame := WordToWord.evaluate_tgt_frame table state.compileOracle state.compile
    state sameDomain program leaf
  have self := WordToWord.evaluate_tgt_frame state.code state.compileOracle state.compile state
    (fun _ => rfl) program leaf
  have oracle := congrArg (fun output => output.2.compileOracle) self
  have compiler := congrArg (fun output => output.2.compile) self
  change (evaluate program state).2.compileOracle = state.compileOracle at oracle
  change (evaluate program state).2.compile = state.compile at compiler
  simpa only [WordToWord.tgtState, ← oracle, ← compiler] using frame

theorem cscLeaf_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64))
    (leaf : WordToWord.cscLeaf p = true) : WordToWord.cscLeaf (applyColour f p) = true := by
  cases p <;> simp_all [applyColour, WordToWord.cscLeaf]

/-- Every non-installing atomic statement: semantic colouring on the common
table, the leaf code frame, and the leaf price bound. -/
theorem colourIndexed_atomic {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (function : Nat) (f : Nat → Nat)
    (sourceFree : WordProps.noInstallCode source)
    (sameDomain : ∀ label, sptMem label target = sptMem label source)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p)
    (prog : WordLangProgHOL (BitVec 64)) (atomic : wordCostAtomic prog = true)
    (semantic : applyColourGoal C F prog) :
    ColourIndexedGoal C F TP SP source target function f prog := by
  intro st cst live lt free sourceCode targetCode ⟨hc, hs, hl⟩
  have leaf : WordToWord.cscLeaf prog = true := by
    cases prog <;> simp_all [wordCostAtomic, WordToWord.cscLeaf, noInstallSubprogsHOL,
      notCreatedSubprogsWithMemOp]
  let down : WordSemStateFiniteExact 64 C F := {cst with code := st.code}
  obtain ⟨permutation, related⟩ := applyColourPost_unpack (semantic st down f live lt ⟨hc, hs, hl⟩)
  have restore : ({down with code := target} : WordSemStateFiniteExact 64 C F) = cst := by
    rw [← targetCode]
  have targetRun : evaluate (applyColour f prog) cst =
      ((evaluate (applyColour f prog) down).1,
        {(evaluate (applyColour f prog) down).2 with code := target}) := by
    have frame := leaf_code_frame (applyColour f prog) down target
      (by intro label; rw [sameDomain label, ← sourceCode]) (cscLeaf_applyColour f prog leaf)
    rw [restore] at frame
    exact frame
  have downCode : (evaluate (applyColour f prog) down).2.code = st.code :=
    code_evaluate (applyColour f prog) down (noInstall_applyColour f prog free)
      (by rw [show down.code = st.code from rfl, sourceCode]; exact sourceFree)
  have sourceRunCode : (evaluate prog {st with permute := permutation}).2.code = st.code :=
    code_evaluate prog {st with permute := permutation} free
      (by rw [show ({st with permute := permutation} : WordSemStateFiniteExact 64 C F).code = st.code from rfl,
        sourceCode]; exact sourceFree)
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  rcases related with bad | ⟨same, frame, locals⟩
  · exact Or.inl bad
  · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · rw [targetRun]; exact same
    · rw [targetRun]
      have shape : ({({(evaluate (applyColour f prog) down).2 with code := target} :
          WordSemStateFiniteExact 64 C F) with code := (evaluate prog {st with permute := permutation}).2.code}) =
          (evaluate (applyColour f prog) down).2 := by
        rw [sourceRunCode, ← downCode]
      rw [shape]
      exact frame
    · rw [targetRun]; exact locals
    · rw [wordExecutionCost_atomic _ _ _ (wordCostAtomic_applyColour f prog atomic),
        wordFunctionExecutionCost_atomic _ _ _ _ atomic]
      exact leafPrice prog

#print axioms indexedPermuteCost
#print axioms indexed_permute_predicate_cost
#print axioms colourIndexed_atomic
#print axioms noInstall_applyColour
#print axioms leaf_code_frame
end InitECandidate.Runtime.FineCost
