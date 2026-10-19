import InitECandidate.Runtime.WitnessAllocationStackHashFrame
import InitECandidate.Runtime.WitnessResultAboveStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Popping a branch retains the saved parents under a concrete below-branch
memory frame. The branch result lies above their saved allocation frontier. -/
theorem WitnessAllocationStack.branch_pop_after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier top previous branch : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (stage : s.memory (top+8)=.word (2 : BitVec 64)) (atBranch : s.memory (top+16)=.word branch)
    (growth : frontier.toNat≤nextFrontier.toNat) (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, top.toNat+88≤watched.toNat → watched.toNat<branch.toNat →
      post.memory watched=s.memory watched) :
    WitnessAllocationStack post input inputLength nextFrontier persistentFloor lower previous ∧
      WitnessResultAboveStack post input inputLength previous branch persistentFloor lower := by
  cases stack with
  | nil => exact False.elim (nonempty rfl)
  | cons parent above valid floorBound parentBound ordered branchAbove tail =>
    have samePrevious := HolWordLab.word.inj (valid.2.2.2.1.symm.trans link)
    subst previous
    obtain ⟨actual,cell,parentBeforeBranch⟩ := branchAbove stage
    have sameBranch := HolWordLab.word.inj (cell.symm.trans atBranch)
    subst actual
    have older := tail.rebase s input inputLength parent _ persistentFloor lower (top.toNat+88) ordered
    have retained := older.after_frame s post input inputLength parent _ persistentFloor (top.toNat+88) domain
      parent lower (Nat.le_refl _) (by omega) (by
        intro watched lo hi
        exact memory watched lo (hi.trans_le parentBeforeBranch))
    have lifted := retained.after_frame post post input inputLength parent _ persistentFloor lower rfl
      nextFrontier lower (parentBound.trans growth) (Nat.le_refl _) (by intro watched lo hi; rfl)
    exact ⟨lifted,Or.inr ⟨parent,parentBeforeBranch,retained⟩⟩

/-- A newly allocated extension result is beyond the entire old heap. A
concrete old-heap memory frame retains all saved parents and their ordering. -/
theorem WitnessAllocationStack.extension_pop_after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier top previous result : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (growth : frontier.toNat≤nextFrontier.toNat) (resultAbove : frontier.toNat≤result.toNat)
    (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, top.toNat+88≤watched.toNat → watched.toNat<frontier.toNat →
      post.memory watched=s.memory watched) :
    WitnessAllocationStack post input inputLength nextFrontier persistentFloor lower previous ∧
      WitnessResultAboveStack post input inputLength previous result persistentFloor lower := by
  cases stack with
  | nil => exact False.elim (nonempty rfl)
  | cons parent above valid floorBound parentBound ordered branchAbove tail =>
    have samePrevious := HolWordLab.word.inj (valid.2.2.2.1.symm.trans link)
    subst previous
    have older := tail.rebase s input inputLength parent _ persistentFloor lower (top.toNat+88) ordered
    have retained := older.after_frame s post input inputLength parent _ persistentFloor (top.toNat+88) domain
      parent lower (Nat.le_refl _) (by omega) (by
        intro watched lo hi
        exact memory watched lo (hi.trans_le parentBound))
    have lifted := retained.after_frame post post input inputLength parent _ persistentFloor lower rfl
      nextFrontier lower (parentBound.trans growth) (Nat.le_refl _) (by intro watched lo hi; rfl)
    exact ⟨lifted,Or.inr ⟨parent,parentBound.trans resultAbove,retained⟩⟩

/-- An extension hash update may touch a previously allocated child below the
current heap. For a nonzero child, its own saved stack frontier supplies the
smaller protected parent interval; zero skips the hash update. -/
theorem WitnessAllocationStack.extension_pop_after_result_hash_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier top previous child result : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (childAbove : WitnessResultAboveStack s input inputLength top child persistentFloor lower)
    (childBound : child.toNat≤frontier.toNat)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (growth : frontier.toNat≤nextFrontier.toNat) (resultAbove : frontier.toNat≤result.toNat)
    (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, top.toNat+88≤watched.toNat → watched.toNat<frontier.toNat →
      (child=0 ∨ watched.toNat<child.toNat) → post.memory watched=s.memory watched) :
    WitnessAllocationStack post input inputLength nextFrontier persistentFloor lower previous ∧
      WitnessResultAboveStack post input inputLength previous result persistentFloor lower := by
  rcases childAbove with zero | ⟨savedFrontier,above,savedStack⟩
  · exact stack.extension_pop_after_frame s post input inputLength frontier nextFrontier top previous result persistentFloor lower
      nonempty link growth resultAbove domain (by intro watched lo hi; exact memory watched lo hi (Or.inl zero))
  · have savedBefore : savedFrontier.toNat≤frontier.toNat := above.trans childBound
    exact savedStack.extension_pop_after_frame s post input inputLength savedFrontier nextFrontier top previous result persistentFloor lower
      nonempty link (savedBefore.trans growth) (savedBefore.trans resultAbove) domain (by
        intro watched lo hi
        exact memory watched lo (hi.trans_le savedBefore) (Or.inr (hi.trans_le above)))

#print axioms WitnessAllocationStack.extension_pop_after_result_hash_frame
#print axioms WitnessAllocationStack.branch_pop_after_frame
#print axioms WitnessAllocationStack.extension_pop_after_frame
end InitECandidate.Runtime
