import InitECandidate.Runtime.WordIselGlobalCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.MaxVar
import Flapjack.Misc.Sptree.Map

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- The concrete per-function instruction-selection table used by the pinned
pipeline: preserve arity and choose maxVar(body)+1 as its fresh temporary. -/
def iselCodeTable (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) : Spt (Nat × WordLangProgHOL (BitVec 64)) :=
  sptMap (fun entry => (entry.1,
    WordInst.instSelectExecutable c (maxVarHOL entry.2 + 1) entry.2)) code

def IselInstallFreeCode (code : Spt (Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  ∀ destination arity body, sptLookup destination code = some (arity, body) → installFree body = true

theorem isel_fresh_variables (program : WordLangProgHOL (BitVec 64)) :
    everyVarHOL (fun x => decide (x < maxVarHOL program + 1)) program = true := by
  exact everyVarMono _ program _ ⟨fun x bounded => by
    simp only [decide_eq_true_eq] at bounded ⊢
    omega, WordAlloc.maxVarMax program⟩

theorem iselCodeTable_related (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (free : IselInstallFreeCode code) :
    IselCode c code (iselCodeTable c code) := by
  intro destination
  constructor
  · simp only [iselCodeTable, sptLookup_sptMap, Option.map_eq_none_iff]
  · intro arity body found
    refine ⟨maxVarHOL body + 1, isel_fresh_variables body, ?_, free destination arity body found⟩
    simp only [iselCodeTable, sptLookup_sptMap, found, Option.map_some]

/-- Concrete whole-table stage endpoint. Neither a freshness witness, an
abstract transformed-code relation nor a guarded callee contract is supplied
by the caller: all three are discharged for the pinned maxVar+1 map. -/
theorem isel_code_table_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64)) (source post : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)) (free : installFree program = true)
    (codeFree : IselInstallFreeCode source.code) (run : evaluate program source = (result, post))
    (safe : result ≠ some .error) :
    ∃ targetPost,
      evaluate (WordInst.instSelectExecutable c (maxVarHOL program + 1) program)
        {source with code := iselCodeTable c source.code} = (result, targetPost) ∧
      IselPost c (maxVarHOL program + 1) result post targetPost ∧
      wordExecutionCost wordOptimizerLocalPrice
        (WordInst.instSelectExecutable c (maxVarHOL program + 1) program)
        {source with code := iselCodeTable c source.code} ≤
      wordExecutionCost (preIselPrice c) program source := by
  apply isel_program_cost c (maxVarHOL program + 1) program free source _ result post
    (isel_fresh_variables program) ?_ run safe
  exact ⟨fun _ _ => rfl, iselCodeTable_related c source.code codeFree, rfl⟩

#print axioms iselCodeTable_related
#print axioms isel_code_table_cost
end InitECandidate.Runtime.FineCost
