import InitECandidate.Runtime.WitnessAllocationStackIndex
import InitECandidate.Runtime.WitnessPhysicalRecordBranchGeometry
import InitECandidate.Runtime.WitnessBranchChildPrefixFrame
import InitECandidate.Runtime.WitnessBranchChildPrefixProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original child-store, occupancy update, increment and dispatch preserve
the full saved allocation order while scheduling the next child. -/
theorem witness_branch_child_prefix_allocation_stack {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top branch index result : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (frontierBound : frontier.toNat≤33806089496)
    (stage : s.memory (top+8)=.word (2 : BitVec 64)) (branchCell : s.memory (top+16)=.word branch)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word branch)))
    (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (beforeLast : index.toNat<15) (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchAt 2)=(none,post)) :
    WitnessAllocationStack post input inputLength frontier persistentFloor lower top ∧
      post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
      post.locals.lookup (ofString "slot")=some (.val (.word (index+1))) ∧
      post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) := by
  have physical := stack.physical s input inputLength frontier top persistentFloor lower
  have geometry : top.toNat+88≤branch.toNat ∧ branch.toNat≤33806089496 := by
    cases physical with
    | nil => exact False.elim (nonempty rfl)
    | cons above valid ordered tail =>
      obtain ⟨array,oldIndex,_,_,_,recordTable,tableBranch,_,branchEnd⟩ := valid.branch_geometry s top _ input inputLength
        frontier branch persistentFloor stage branchCell
      exact ⟨by omega,by omega⟩
  obtain ⟨topPost,slotPost,modePost,indexPost,globalsPost,credit⟩ := witness_branch_child_prefix_normal_progress
    s post top branch index result atTop atBr atResult atIndex beforeLast code run
  have framed := witness_branch_child_prefix_normal_memory_frame s post top branch index result
    atTop atBr atIndex atResult beforeLast code run
  have metadata := evaluateHOLFiniteState_metadata s (witnessBranchAt 2)
  rw [run] at metadata
  have addNat (base : BitVec 64) (offset : Nat) (small : base.toNat+offset<2^64) :
      (base+BitVec.ofNat 64 offset).toNat=base.toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega),Nat.mod_eq_of_lt small]
  have topNat (offset : Nat) (inside : offset<88) := addNat top offset (by omega)
  have top40Nat : (top+(40 : BitVec 64)).toNat=top.toNat+40 := topNat 40 (by decide)
  have top32Nat : (top+32#64).toNat=top.toNat+32 := topNat 32 (by decide)
  have branch32Nat : (branch+(32 : BitVec 64)).toNat=branch.toNat+32 := addNat branch 32 (by omega)
  have productNat : (index*(8 : BitVec 64)).toNat=index.toNat*8 := by
    rw [BitVec.toNat_mul]
    change (index.toNat*8)%2^64=index.toNat*8
    exact Nat.mod_eq_of_lt (by omega)
  have childNat : (branch+32+index*8).toNat=branch.toNat+32+index.toNat*8 := by
    rw [BitVec.toNat_add,branch32Nat,productNat]
    exact Nat.mod_eq_of_lt (by omega)
  have nextNat : (index+1).toNat=index.toNat+1 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; omega)]; rfl
  refine ⟨stack.after_branch_index s post input inputLength frontier frontier top branch (index+1) persistentFloor lower
    nonempty stage branchCell (Nat.le_refl _) metadata.2.1 (by rw [nextNat]; omega) indexPost ?_ ?_,topPost,slotPost,modePost⟩
  · intro offset inside notIndex notOcc notHash
    apply framed
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [topNat offset inside,childNat] at equal
      omega
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [topNat offset inside,top40Nat] at equal
      omega
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [topNat offset inside,top32Nat] at equal
      omega
  · intro watched afterRecord beforeBranch
    apply framed
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [childNat] at equal
      omega
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [top40Nat] at equal
      omega
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [top32Nat] at equal
      omega

#print axioms witness_branch_child_prefix_allocation_stack
end InitECandidate.Runtime
