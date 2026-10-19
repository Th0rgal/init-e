import InitECandidate.Runtime.WitnessPhysicalStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Each record saves the heap frontier that preceded its own decoding. All
parent tables fit below that frontier, and its branch constructor lies above
it. These facts survive later allocations and justify a branch result on pop. -/
inductive WitnessAllocationStack {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength : BitVec 64) : BitVec 64 → Nat → Nat → BitVec 64 → Prop
  | nil {frontier : BitVec 64} {persistentFloor lower : Nat} : WitnessAllocationStack s input inputLength frontier persistentFloor lower 0
  | cons {frontier : BitVec 64} {persistentFloor lower : Nat} {record previous : BitVec 64} (parentFrontier : BitVec 64)
      (above : lower≤record.toNat)
      (valid : WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor)
      (floorBound : persistentFloor≤parentFrontier.toNat)
      (parentBound : parentFrontier.toNat≤frontier.toNat)
      (ordered : previous=0 ∨ record.toNat+88≤previous.toNat)
      (branchAbove : s.memory (record+8)=.word (2 : BitVec 64) →
        ∃ branch : BitVec 64, s.memory (record+16)=.word branch ∧ parentFrontier.toNat≤branch.toNat)
      (tail : WitnessAllocationStack s input inputLength parentFrontier persistentFloor lower previous) :
      WitnessAllocationStack s input inputLength frontier persistentFloor lower record

theorem WitnessAllocationStack.lower {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top : BitVec 64) (persistentFloor lower nextLower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (moves : nextLower≤lower) :
    WitnessAllocationStack s input inputLength frontier persistentFloor nextLower top := by
  induction stack with
  | nil => exact .nil
  | cons parent above valid floorBound parentBound ordered branchAbove tail ih =>
    exact .cons parent (by omega) valid floorBound parentBound ordered branchAbove (ih moves)

/-- Forgetting saved allocation frontiers retains the existing physical stack. -/
theorem WitnessAllocationStack.physical {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top) :
    WitnessPhysicalStack s input inputLength frontier persistentFloor lower top := by
  induction stack with
  | nil => exact .nil
  | @cons frontier persistentFloor lower record previous parent above valid floorBound parentBound ordered branchAbove tail ih =>
    have lifted := ih.after_frame s s input inputLength parent frontier previous persistentFloor lower lower
      floorBound parentBound (Nat.le_refl _) rfl (by intro w lo hi; rfl)
    exact .cons above valid ordered lifted

/-- Fresh source metadata establishes the branch-versus-parent-frontier fact;
this is stronger than merely placing the branch above the persistent floor. -/
theorem placed_pushed_branch_above {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record pointer length input inputLength frontier : BitVec 64) (ceiling : Nat)
    (valid : DecoderPlacedPushedTable s record pointer length input inputLength ceiling frontier.toNat)
    (stage : s.memory (record+8)=.word (2 : BitVec 64)) :
    ∃ branch : BitVec 64, s.memory (record+16)=.word branch ∧ frontier.toNat≤branch.toNat := by
  obtain ⟨array,branch,heap,_,cell,above,_,_,_,_,_⟩ := valid.2 stage
  exact ⟨branch,cell,above⟩

theorem WitnessAllocationStack.push {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier record previous : BitVec 64) (persistentFloor lower nextLower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower previous)
    (valid : WitnessPhysicalRecord s record previous input inputLength nextFrontier persistentFloor)
    (floorBound : persistentFloor≤frontier.toNat) (growth : frontier.toNat≤nextFrontier.toNat)
    (fresh : record.toNat+88≤lower) (nextAbove : nextLower≤record.toNat)
    (branchAbove : s.memory (record+8)=.word (2 : BitVec 64) →
      ∃ branch : BitVec 64, s.memory (record+16)=.word branch ∧ frontier.toNat≤branch.toNat) :
    WitnessAllocationStack s input inputLength nextFrontier persistentFloor nextLower record := by
  apply WitnessAllocationStack.cons frontier nextAbove valid floorBound growth
  · cases stack with
    | nil => exact Or.inl rfl
    | cons parent above parentValid pf pb ordered geometry tail => exact Or.inr (by omega)
  · exact branchAbove
  · exact stack.lower s input inputLength frontier previous persistentFloor lower nextLower (by omega)

/-- A real branch parent-pop exposes a saved frontier bounding the complete
retained parent stack from above and the returned branch from below. -/
theorem WitnessAllocationStack.branch_parent {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top previous branch : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (stage : s.memory (top+8)=.word (2 : BitVec 64)) (atBranch : s.memory (top+16)=.word branch) :
    ∃ parentFrontier : BitVec 64,
      persistentFloor≤parentFrontier.toNat ∧ parentFrontier.toNat≤branch.toNat ∧
      WitnessAllocationStack s input inputLength parentFrontier persistentFloor lower previous := by
  cases stack with
  | nil => exact False.elim (nonempty rfl)
  | cons parent above valid floorBound parentBound ordered branchAbove tail =>
    have same := HolWordLab.word.inj (valid.2.2.2.1.symm.trans link)
    subst previous
    obtain ⟨actual,cell,bound⟩ := branchAbove stage
    have sameBranch := HolWordLab.word.inj (cell.symm.trans atBranch)
    subst actual
    exact ⟨parent,floorBound,bound,tail⟩

#print axioms WitnessAllocationStack.physical
#print axioms placed_pushed_branch_above
#print axioms WitnessAllocationStack.push
#print axioms WitnessAllocationStack.branch_parent
end InitECandidate.Runtime
