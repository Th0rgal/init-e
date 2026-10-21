import InitECandidate.Runtime.FullSSACodeTable
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact

/-- A mapped-table result/frame/locals/cost relation for composition. -/
def SSAQuantitativeMappedOutcome {C F : Type} (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F)
    (sourceWork targetWork : Nat) : Prop :=
  source.1 = some .error ∨ source.1 = target.1 ∧
    FullSSATableFrame source.2 target.2 ∧
    SSAResultLocals next map tables source.2.locals target.2.locals source.1 ∧ targetWork ≤ sourceWork

/-- Quantitative local SSA simulation over the real mapped callee table.
The original result-sensitive locals relation is retained; a root-only entry
allowance remains explicit. No callee execution is a field of this relation. -/
def SSAQuantitativeMappedAllowance {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (program : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (entry : Nat) : Prop :=
  ∃ permutation : Nat → Nat → Nat,
    let compiled := ssaCcTrans program map next tables
    let sourceState := {source with permute := permutation}
    let sourceRun := evaluate program sourceState
    let targetRun := evaluate compiled.1 target
    sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
      FullSSATableFrame sourceRun.2 targetRun.2 ∧
      SSAResultLocals compiled.2.2 compiled.2.1 tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
      wordExecutionCost (fun p _ => TP p) compiled.1 target ≤
        wordExecutionCost (fun p _ => SP p) program sourceState + entry

def SSAMappedBodyAllowance {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (body : WordLangProgHOL (BitVec 64))
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) (entry : Nat) : Prop :=
  ∀ (source target : WordSemStateFiniteExact 64 C F),
    FullSSATableFrame source target ∧ ssaLocalsRel next map source.locals target.locals ∧
    isAllocVar next ∧ everyVarHOL (fun key => decide (key < next)) body = true ∧
    ssaMapOK next map ∧ ltOK tables → WordProps.noInstallCode source.code →
    SSAQuantitativeMappedAllowance SP TP body source target map next tables entry

#print axioms SSAQuantitativeMappedAllowance
#print axioms SSAMappedBodyAllowance
end InitECandidate.Runtime.FineCost
