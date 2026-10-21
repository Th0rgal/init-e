import InitECandidate.Runtime.SSAInstructionExecutedCost
import InitECandidate.Runtime.WordStackValueGlobalCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
set_option maxHeartbeats 5000000

/-- The original result-sensitive SSA locals relation. Only fall-through
uses the output map/counter; loop exits use the actual enclosing table. -/
def SSAResultLocals {α : Type} (next : Nat) (map : Spt Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (source target : Spt α) :
    Option (WordSemResult 64) → Prop
  | none => ssaLocalsRel next map source target
  | some (.break label) => match tables[label]? with
    | none => True
    | some (dest, _, exits) => Flapjack.WordAlloc.strongLocalsRel
      (optionLookup dest) (sptDomain exits) source target
  | some (.continue label) => match tables[label]? with
    | none => True
    | some (dest, entries, _) => Flapjack.WordAlloc.strongLocalsRel
      (optionLookup dest) (sptDomain entries) source target
  | some _ => source = target

/-- Quantitative SSA simulation. The semantic result, complete frame,
result-sensitive locals and work bound all use ONE existential source
permutation. The actual compiler supplies the output syntax and map.
Pure prices remain parameters, allowing tighter post-colouring prices. -/
def SSAQuantitativeSimulation {C F : Type}
    (sourcePrice targetPrice : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Prop :=
  ∃ permutation : Nat → Nat → Nat,
    let compiled := ssaCcTrans program map next tables
    let sourceState := {source with permute := permutation}
    let sourceRun := evaluate program sourceState
    let targetRun := evaluate compiled.1 target
    sourceRun.1 = some .error ∨
      sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
      SSAResultLocals compiled.2.2 compiled.2.1 tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
      wordExecutionCost (fun p _ => targetPrice p) compiled.1 target ≤
        wordExecutionCost (fun p _ => sourcePrice p) program sourceState

/-- Extract the original witness without changing its error exemption or
result relation. This is semantic extraction, not a quantitative assumption. -/
theorem ssa_semantic_witness {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (simulation : ssaSimulation program source target map next tables) :
    ∃ permutation : Nat → Nat → Nat,
      let compiled := ssaCcTrans program map next tables
      let sourceRun := evaluate program {source with permute := permutation}
      let targetRun := evaluate compiled.1 target
      sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        SSAResultLocals compiled.2.2 compiled.2.1 tables sourceRun.2.locals targetRun.2.locals sourceRun.1 := by
  obtain ⟨permutation, related⟩ := simulation
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  by_cases error : (evaluate program {source with permute := permutation}).1 = some .error
  · exact Or.inl error
  · right
    simp only [error, if_false] at related
    refine ⟨related.1, related.2.1, ?_⟩
    have locals := related.2.2
    generalize resultEq : (evaluate program {source with permute := permutation}).1 = outcome at locals ⊢
    cases outcome with
    | none => exact locals
    | some value => cases value <;> exact locals

/-- Forgetting work recovers the original SSA theorem with the same witness. -/
theorem SSAQuantitativeSimulation.semantic {C F : Type}
    {sourcePrice targetPrice : WordLangProgHOL (BitVec 64) → Nat}
    {program : WordLangProgHOL (BitVec 64)} {source target : WordSemStateFiniteExact 64 C F}
    {map : Spt Nat} {next : Nat} {tables : List (Spt Nat × Spt Unit × Spt Unit)}
    (simulation : SSAQuantitativeSimulation sourcePrice targetPrice program source target map next tables) :
    ssaSimulation program source target map next tables := by
  obtain ⟨permutation, related⟩ := simulation
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  by_cases error : (evaluate program {source with permute := permutation}).1 = some .error
  · simp only [error, if_true]
  · simp only [error, if_false]
    rcases related with bad | ⟨result, frame, locals, cost⟩
    · exact (error bad).elim
    · refine ⟨result, frame, ?_⟩
      generalize resultEq : (evaluate program {source with permute := permutation}).1 = outcome at locals ⊢
      cases outcome with
      | none => exact locals
      | some value => cases value <;> exact locals

/-- All integer instructions instantiate the quantitative interface. The
only price premise is a static source-node inequality. The actual emitted
moves, compiler output and target work bound are proved by the checked
instruction theorem; they are not supplied by a caller. -/
theorem ssa_quantitative_instruction {C F : Type}
    (sourcePrice : WordLangProgHOL (BitVec 64) → Nat)
    (instruction : WordLangInst (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst instruction) = true ∧
      ssaMapOK next map ∧ ltOK tables)
    (price : max 24 (WordToStack.refinedNativeInstructionPrice (HolInst.ofWordLangInst instruction)) +
      ssaInstructionMovePrice instruction ≤ sourcePrice (.inst instruction)) :
    SSAQuantitativeSimulation sourcePrice (fun p => wordOptimizerLocalPrice p source)
      (.inst instruction) source target map next tables := by
  obtain ⟨semantics, work⟩ := ssa_instruction_semantics_and_cost instruction source target map next tables premises
  obtain ⟨permutation, related⟩ := ssa_semantic_witness (.inst instruction) source target map next tables semantics
  refine ⟨permutation, ?_⟩
  rcases related with error | ⟨result, frame, locals⟩
  · exact Or.inl error
  · refine Or.inr ⟨result, frame, locals, ?_⟩
    have prices : (fun (p : WordLangProgHOL (BitVec 64)) (_ : WordSemStateFiniteExact 64 C F) =>
        wordOptimizerLocalPrice p source) = wordOptimizerLocalPrice := by
      funext p state
      exact wordOptimizerLocalPrice_state_independent p source state
    rw [prices]
    have bound := work permutation
    rw [wordExecutionCost_atomic _ (.inst instruction) _ rfl] at bound ⊢
    exact bound.trans price

#print axioms ssa_semantic_witness
#print axioms SSAQuantitativeSimulation.semantic
#print axioms ssa_quantitative_instruction
end InitECandidate.Runtime.FineCost
