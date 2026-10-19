import InitECandidate.Runtime.WitnessAllocationStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The actual saved-link chain stays below the original scratch ceiling.
This bound is independent of the higher persistent-node allocation floor. -/
inductive WitnessScratchChain {F : Type} (s : PanSemStateFiniteExact 64 F) (upper lower : Nat) : BitVec 64 → Prop
  | nil : WitnessScratchChain s upper lower 0
  | cons {record previous : BitVec 64} (above : lower≤record.toNat)
      (positive : 0<record.toNat) (before : record.toNat+88≤upper)
      (link : s.memory record=.word previous)
      (ordered : previous=0 ∨ record.toNat+88≤previous.toNat)
      (tail : WitnessScratchChain s upper lower previous) : WitnessScratchChain s upper lower record

theorem WitnessScratchChain.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top : BitVec 64) (upper lower nextLower : Nat) (chain : WitnessScratchChain s upper lower top)
    (lowerMoves : nextLower≤lower)
    (memory : ∀ watched : BitVec 64, lower≤watched.toNat → watched.toNat<upper → post.memory watched=s.memory watched) :
    WitnessScratchChain post upper nextLower top := by
  induction chain with
  | nil => exact .nil
  | cons above positive before link ordered tail ih =>
    exact .cons (by omega) positive before ((memory _ above (by omega)).trans link) ordered ih

theorem WitnessScratchChain.rebase {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top : BitVec 64) (upper lower nextLower : Nat) (chain : WitnessScratchChain s upper lower top)
    (bound : top=0 ∨ nextLower≤top.toNat) : WitnessScratchChain s upper nextLower top := by
  revert bound
  induction chain with
  | nil => intro _; exact .nil
  | @cons record previous above positive before link ordered tail ih =>
    intro bound
    have nonzero : record≠0 := by intro zero; rw [zero] at positive; cases positive
    have lo := bound.resolve_left nonzero
    refine .cons lo positive before link ordered (ih ?_)
    rcases ordered with zero | aboveParent
    · exact Or.inl zero
    · exact Or.inr (by omega)

theorem WitnessScratchChain.push {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record previous : BitVec 64) (upper lower nextLower : Nat) (chain : WitnessScratchChain s upper lower previous)
    (positive : 0<record.toNat) (fresh : record.toNat+88≤lower) (oldBelow : lower≤upper)
    (nextAbove : nextLower≤record.toNat) (link : s.memory record=.word previous) :
    WitnessScratchChain s upper nextLower record := by
  apply WitnessScratchChain.cons nextAbove positive (by omega) link
  · cases chain with
    | nil => exact Or.inl rfl
    | cons above oldPositive before oldLink ordered tail => exact Or.inr (by omega)
  · exact chain.after_frame s s previous upper lower nextLower (by omega) (by intro w lo hi; rfl)

theorem WitnessScratchChain.pop_after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top previous : BitVec 64) (upper lower : Nat) (chain : WitnessScratchChain s upper lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (memory : ∀ watched : BitVec 64, top.toNat+88≤watched.toNat → watched.toNat<upper →
      post.memory watched=s.memory watched) : WitnessScratchChain post upper lower previous := by
  cases chain with
  | nil => exact False.elim (nonempty rfl)
  | cons above positive before oldLink ordered tail =>
    have same := HolWordLab.word.inj (oldLink.symm.trans link)
    subst previous
    have older := tail.rebase s _ upper lower (top.toNat+88) ordered
    exact older.after_frame s post _ upper (top.toNat+88) lower (by omega) memory

#print axioms WitnessScratchChain.after_frame
#print axioms WitnessScratchChain.rebase
#print axioms WitnessScratchChain.push
#print axioms WitnessScratchChain.pop_after_frame
end InitECandidate.Runtime
