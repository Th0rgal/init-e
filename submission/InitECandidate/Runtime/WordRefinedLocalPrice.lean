import InitECandidate.Runtime.WordExecutionCostCorrect
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Canonical local price from the checked Word-to-Stack fragments. Move
costs retain exact physical scheduler length; calls use their actual arities. -/
noncomputable def refinedWordLocalPrice {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (_source : WordSemStateFiniteExact 64 C F) : Nat :=
  match refinedWordStackLeafBudget program with
  | some budget => budget
  | none => match program with
    | .ite _ _ _ _ _ => 23
    | .loop _ _ _ => 2
    | .call none _ _ _ => 41
    | .call (some (values,_,_,_,_)) _ args handler =>
        (if handler.isSome then 189 else 63)+39*(args.length+1-22)+21*(values.length+1-22)
    | _ => 0

theorem refinedWordLocalPrice_caps {F : Type} :
    FineWordCostCaps (refinedWordLocalPrice (C := Nat × LabToTarget.Config) (F := F)) 1 := by
  constructor
  · intro program source budget priced
    simp only [refinedWordLocalPrice,priced,Nat.one_mul,Nat.le_refl]
  · intro first second source
    rfl
  · intro cmp reg operand first second source
    simp [refinedWordLocalPrice,refinedWordStackLeafBudget]
  · intro names body exitNames source
    simp [refinedWordLocalPrice,refinedWordStackLeafBudget]
  · intro dest args handler source
    simp [refinedWordLocalPrice,refinedWordStackLeafBudget]
  · intro values names retCode l1 l2 dest args source
    simp [refinedWordLocalPrice,refinedWordStackLeafBudget]
  · intro values names retCode l1 l2 dest args handlerVar handlerCode h1 h2 source
    simp [refinedWordLocalPrice,refinedWordStackLeafBudget]

/-- Whole compiler cost bound for the concrete canonical Word price. All
local price obligations are discharged here rather than assumed by a caller. -/
theorem refinedWordCost_correct {F : Type} (ac : AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (supported : wordCostSupported program = true)
    (code : CostSupportedCode source.code)
    (frames : CodeFramesBounded source.code source.stackSize 92) :
    RefinedExecutedSimulation ac program source
      (wordExecutionCost refinedWordLocalPrice program source) := by
  simpa only [Nat.one_mul] using
    wordExecutionCost_correct ac refinedWordLocalPrice 1 refinedWordLocalPrice_caps program source supported code frames

#print axioms refinedWordLocalPrice_caps
#print axioms refinedWordCost_correct
end InitECandidate.Runtime.WordToStack
