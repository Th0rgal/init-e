import InitECandidate.Runtime.MerkleizeSource
import InitECandidate.Runtime.Sha256PairBound
import InitECandidate.Runtime.VariableCountedDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merklePair_counted : CountedBody (ofString "j") 1 merklePairBody (136 + 0) := by
  rw [source_merklePair_body]
  exact CountedBody.seq _ (ProgBounded.call sha256Pair_funBounded _ _)
    (by decide) (by decide) CountedBody.incr

/-- A uniform finite level bound, including malformed states and every exit.
The source-input bounds permit tighter instantiations during composition. -/
def merkleLevelCost : Nat := (2 ^ 64 - 1) * 137

theorem merkleLevel_body_bounded : ProgBounded merkleLevelBody merkleLevelCost := by
  rw [source_merkleLevel_body]
  apply ProgBounded.weaken
  · apply ProgBounded.dec
    apply ProgBounded.variableCountedDec (ofString "j") (ofString "half") .less (Or.inl rfl)
      merklePair_counted (by decide)
    exact ProgBounded.straight _ (by decide)
  · decide

#print axioms merklePair_counted
#print axioms merkleLevel_body_bounded
end InitECandidate.Runtime
