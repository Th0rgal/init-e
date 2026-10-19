import InitECandidate.Runtime.WitnessAllocationStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Old protected memory preserves saved allocation frontiers as well as the
physical links; parent frontiers remain fixed when the current heap grows. -/
theorem WitnessAllocationStack.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (domain : post.memaddrs=s.memaddrs) :
    ∀ (nextFrontier : BitVec 64) (nextLower : Nat), frontier.toNat≤nextFrontier.toNat → nextLower≤lower →
      (∀ watched : BitVec 64, lower≤watched.toNat → watched.toNat<frontier.toNat → post.memory watched=s.memory watched) →
      WitnessAllocationStack post input inputLength nextFrontier persistentFloor nextLower top := by
  induction stack with
  | nil => intro nextFrontier nextLower growth lowerMoves memory; exact .nil
  | @cons frontier persistentFloor lower record previous parent above valid floorBound parentBound ordered branchAbove tail ih =>
    intro nextFrontier nextLower growth lowerMoves memory
    have before := valid.2.1
    have floorBeforeHeap : persistentFloor≤frontier.toNat := floorBound.trans parentBound
    have wordMemory (offset : Nat) (inside : offset<88) :
        post.memory (record+BitVec.ofNat 64 offset)=s.memory (record+BitVec.ofNat 64 offset) := by
      have address : (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset := by
        have topBound := frontier.isLt
        rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      exact memory _ (by rw [address]; omega) (by rw [address]; omega)
    have recordPost := valid.after_frame s post record previous input inputLength frontier nextFrontier persistentFloor
      growth domain (by intro offset inside _ _; exact wordMemory offset inside)
      (by intro watched lo hi; exact memory watched (by omega) hi)
    have tailPost := ih parent nextLower (Nat.le_refl _) lowerMoves (by
      intro watched lo hi
      exact memory watched lo (hi.trans_le parentBound))
    refine .cons parent (by omega) recordPost floorBound (parentBound.trans growth) ordered ?_ tailPost
    intro stage
    have stageFrame : post.memory (record+8)=s.memory (record+8) := by simpa using wordMemory 8 (by decide)
    have branchFrame : post.memory (record+16)=s.memory (record+16) := by simpa using wordMemory 16 (by decide)
    obtain ⟨branch,cell,bound⟩ := branchAbove (stageFrame.symm.trans stage)
    exact ⟨branch,branchFrame.trans cell,bound⟩

#print axioms WitnessAllocationStack.after_frame
end InitECandidate.Runtime
