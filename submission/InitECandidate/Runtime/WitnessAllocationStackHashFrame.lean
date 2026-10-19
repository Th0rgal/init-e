import InitECandidate.Runtime.WitnessAllocationStackFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every older parent lies above the current record, so the chain can be
viewed from any lower frontier below its first nonempty record. -/
theorem WitnessAllocationStack.rebase {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top : BitVec 64) (persistentFloor lower nextLower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (bound : top=0 ∨ nextLower≤top.toNat) :
    WitnessAllocationStack s input inputLength frontier persistentFloor nextLower top := by
  revert bound
  induction stack with
  | nil => intro _; exact .nil
  | @cons frontier persistentFloor lower record previous parent above valid floorBound parentBound ordered branchAbove tail ih =>
    intro bound
    have positive := valid.1
    have nonzero : record≠0 := by intro zero; rw [zero] at positive; cases positive
    have below := bound.resolve_left nonzero
    refine .cons parent below valid floorBound parentBound ordered branchAbove (ih ?_)
    rcases ordered with empty | later
    · exact Or.inl empty
    · exact Or.inr (by omega)

/-- Updating only the current record hash field preserves every live record
and slice table, including the higher-address saved parents. -/
theorem WitnessAllocationStack.after_top_hash_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier top : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (floorBeforeHeap : persistentFloor≤frontier.toNat) (growth : frontier.toNat≤nextFrontier.toNat)
    (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, lower≤watched.toNat → watched.toNat<frontier.toNat → watched≠top+80 →
      post.memory watched=s.memory watched) :
    WitnessAllocationStack post input inputLength nextFrontier persistentFloor lower top := by
  cases stack with
  | nil => exact .nil
  | @cons _ _ _ _ previous parent above valid floorBound parentBound ordered branchAbove tail =>
    have recordBefore := valid.2.1
    have addNat (offset : Nat) (inside : offset<88) :
        (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
      have upper := frontier.isLt
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have hashNat : (top+(80 : BitVec 64)).toNat=top.toNat+80 := by
      exact addNat 80 (by decide)
    have recordPost := valid.after_frame s post top previous input inputLength frontier nextFrontier persistentFloor growth domain
      (by
        intro offset inside notOcc notHash
        apply memory
        · rw [addNat offset inside]; omega
        · rw [addNat offset inside]; omega
        · intro same
          have equal := congrArg BitVec.toNat same
          rw [addNat offset inside,hashNat] at equal
          omega)
      (by
        intro watched afterRecord beforeHeap
        apply memory watched (by omega) beforeHeap
        intro same
        have equal := congrArg BitVec.toNat same
        rw [hashNat] at equal
        omega)
    have older := tail.rebase s input inputLength parent previous persistentFloor lower (top.toNat+88) ordered
    have olderPost := older.after_frame s post input inputLength parent previous persistentFloor
      (top.toNat+88) domain parent lower (Nat.le_refl _) (by omega) (by
        intro watched afterRecord beforeHeap
        apply memory watched (by omega) (beforeHeap.trans_le parentBound)
        intro same
        have equal := congrArg BitVec.toNat same
        rw [hashNat] at equal
        omega)
    refine .cons parent above recordPost floorBound (parentBound.trans growth) ordered ?_ olderPost
    intro stage
    have fieldMemory (offset : Nat) (inside : offset<88) (notHash : offset≠80) :
        post.memory (top+BitVec.ofNat 64 offset)=s.memory (top+BitVec.ofNat 64 offset) := by
      apply memory
      · rw [addNat offset inside]; omega
      · rw [addNat offset inside]; omega
      · intro same
        have equal := congrArg BitVec.toNat same
        rw [addNat offset inside,hashNat] at equal
        omega
    have stageFrame : post.memory (top+8)=s.memory (top+8) := by simpa using fieldMemory 8 (by decide) (by decide)
    have branchFrame : post.memory (top+16)=s.memory (top+16) := by simpa using fieldMemory 16 (by decide) (by decide)
    obtain ⟨branch,cell,bound⟩ := branchAbove (stageFrame.symm.trans stage)
    exact ⟨branch,branchFrame.trans cell,bound⟩

#print axioms WitnessAllocationStack.rebase
#print axioms WitnessAllocationStack.after_top_hash_frame
end InitECandidate.Runtime
