import InitECandidate.Runtime.WordCostSupported
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

/-- Local, syntax-sized compiler obligations. These are independent of any
target execution or whole-run bound and preserve one coefficient under composition. -/
structure FineWordCostCaps {F : Type}
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat) (factor : Nat) : Prop where
  leaf : ∀ program source budget, refinedWordStackLeafBudget program = some budget →
    budget ≤ factor * price program source
  seqFree : ∀ first second source, price (.seq first second) source = 0
  condition : ∀ cmp reg operand first second source,
    23 ≤ factor * price (.ite cmp reg operand first second) source
  loop : ∀ names body exitNames source,
    2 ≤ factor * price (.loop names body exitNames) source
  tail : ∀ dest args handler source, 41 ≤ factor * price (.call none dest args handler) source
  returning : ∀ values names retCode l1 l2 dest args source,
    63+39*(args.length+1-22)+21*(values.length+1-22) ≤
      factor * price (.call (some (values,names,retCode,l1,l2)) dest args none) source
  handler : ∀ values names retCode l1 l2 dest args handlerVar handlerCode h1 h2 source,
    189+39*(args.length+1-22)+21*(values.length+1-22) ≤
      factor * price (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source
#print axioms FineWordCostCaps
end InitECandidate.Runtime.WordToStack
