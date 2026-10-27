import InitECandidate.Proofs.ComputationCache
import Flapjack.Compiler.Backend.WordCse.Transform
namespace InitECandidate.Proofs.CseComputation
open Flapjack Flapjack.Compiler.Backend

theorem seq_of_eq {width : Nat} [NeZero width]
    (input middle output : WordCse.Knowledge)
    (p q pOut qOut : WordLangProgHOL (BitVec width))
    (hp : WordCse.wordCse input p = (middle,pOut))
    (hq : WordCse.wordCse middle q = (output,qOut)) :
    WordCse.wordCse input (.seq p q) = (output,.seq pOut qOut) := by
  simp only [WordCse.wordCse, hp, hq]

theorem ite_of_eq {width : Nat} [NeZero width]
    (input left right : WordCse.Knowledge)
    (comparison : Cmp) (condition : Nat) (immediate : WordRegImm (BitVec width))
    (p q pOut qOut : WordLangProgHOL (BitVec width))
    (hp : WordCse.wordCse input p = (left,pOut))
    (hq : WordCse.wordCse input q = (right,qOut)) :
    WordCse.wordCse input (.ite comparison condition immediate p q) =
      (WordCse.mergeData left right, .ite comparison condition immediate pOut qOut) := by
  simp only [WordCse.wordCse, hp, hq]

theorem seq_boxed_of_eq {width : Nat} [NeZero width]
    (input middle output : WordCse.Knowledge)
    (p q pOut qOut : WordLangProgHOL (BitVec width))
    (hp : WordCse.wordCse input p = (middle,pOut))
    (hq : WordCse.wordCse middle q = (output,qOut)) :
    WordCse.wordCse input (.seq p q) =
      (output,(ComputationCache.boxedValue (.seq pOut qOut)).val) := by
  rw [ComputationCache.boxedValue_eq]
  exact seq_of_eq input middle output p q pOut qOut hp hq

#print axioms seq_of_eq

theorem ite_checkpoint {width : Nat} [NeZero width]
    (input left right output : WordCse.Knowledge)
    (comparison : Cmp) (condition : Nat) (immediate : WordRegImm (BitVec width))
    (p q pOut qOut : WordLangProgHOL (BitVec width))
    (hp : WordCse.wordCse input p = (left,pOut))
    (hq : WordCse.wordCse input q = (right,qOut))
    (merge : WordCse.mergeData left right = output) :
    WordCse.wordCse input (.ite comparison condition immediate p q) =
      (output,.ite comparison condition immediate pOut qOut) := by
  rw [ite_of_eq input left right comparison condition immediate p q pOut qOut hp hq, merge]

theorem mustTerminate_of_eq {width : Nat} [NeZero width]
    (input output : WordCse.Knowledge) (p q : WordLangProgHOL (BitVec width))
    (h : WordCse.wordCse input p = (output,q)) :
    WordCse.wordCse input (.mustTerminate p) = (output,.mustTerminate q) := by
  simp only [WordCse.wordCse, h]

theorem loop_of_eq {width : Nat} [NeZero width]
    (input output : WordCse.Knowledge) (names exits : WordLangNumSetHOL)
    (p q : WordLangProgHOL (BitVec width))
    (h : WordCse.wordCse WordCse.emptyData p = (output,q)) :
    WordCse.wordCse input (.loop names p exits) = (WordCse.emptyData,.loop names q exits) := by
  simp only [WordCse.wordCse, h]

#print axioms ite_of_eq
#print axioms seq_boxed_of_eq
end InitECandidate.Proofs.CseComputation
