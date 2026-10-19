import InitECandidate.Runtime.WitnessBranchChildPrefixFrame
import InitECandidate.Runtime.WitnessBranchChildPrefixProgress
import InitECandidate.Runtime.WitnessTraversalChildCredit
import InitECandidate.Runtime.DecodeWitnessTraversalMeasure
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual child delivery decreases the measure using the child credit
read from its real saved index and its unchanged scratch capacity. -/
theorem witness_branch_child_prefix_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top branch index result frame : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word branch)))
    (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (nonempty : top≠0) (recordBeforeBranch : top.toNat+88≤branch.toNat)
    (branchBound : branch.toNat≤33806089496)
    (stage : s.memory (top+8)=.word (2 : BitVec 64)) (savedIndex : s.memory (top+32)=.word index)
    (beforeLast : index.toNat<15) (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchAt 2)=(none,post)) :
    decodeWitnessMeasure (decoderScratchCapacity frame post) top (witnessTraversalChildCredit post top) 3 <
      decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 1 := by
  obtain ⟨topPost,slotPost,modePost,indexPost,globalsPost,credit⟩ := witness_branch_child_prefix_normal_progress
    s post top branch index result atTop atBr atResult atIndex beforeLast code run
  have memory := witness_branch_child_prefix_normal_memory_frame s post top branch index result
    atTop atBr atIndex atResult beforeLast code run
  have topNat : (top+(8 : BitVec 64)).toNat=top.toNat+8 := by
    rw [BitVec.toNat_add]
    change (top.toNat+8)%2^64=top.toNat+8
    exact Nat.mod_eq_of_lt (by omega)
  have branchNat : (branch+(32 : BitVec 64)).toNat=branch.toNat+32 := by
    rw [BitVec.toNat_add]
    change (branch.toNat+32)%2^64=branch.toNat+32
    exact Nat.mod_eq_of_lt (by omega)
  have productNat : (index*(8 : BitVec 64)).toNat=index.toNat*8 := by
    rw [BitVec.toNat_mul]
    change (index.toNat*8)%2^64=index.toNat*8
    exact Nat.mod_eq_of_lt (by omega)
  have childNat : (branch+32+index*8).toNat=branch.toNat+32+index.toNat*8 := by
    rw [BitVec.toNat_add,branchNat,productNat]
    exact Nat.mod_eq_of_lt (by omega)
  have stageFrame : post.memory (top+8)=s.memory (top+8) := by
    apply memory
    · intro same
      have equal := congrArg BitVec.toNat same
      rw [topNat,childNat] at equal
      omega
    · intro same
      have impossible : (8 : BitVec 64)=40 := by simpa using same
      exact (by decide : (8 : BitVec 64)≠40) impossible
    · intro same
      have impossible : (8 : BitVec 64)=32#64 := by simpa using same
      exact (by decide : (8 : BitVec 64)≠32#64) impossible
  have oldCredit := witnessTraversalChildCredit_branch s top index nonempty stage savedIndex
  have newCredit := witnessTraversalChildCredit_branch post top (index+1) nonempty (stageFrame.trans stage) indexPost
  have capacity : decoderScratchCapacity frame post=decoderScratchCapacity frame s := by
    simp only [decoderScratchCapacity,globalsPost]
  rw [capacity]
  apply decodeWitnessMeasure_child
  · rw [oldCredit,newCredit]; exact credit
  · decide

#print axioms witness_branch_child_prefix_measure_decreases
end InitECandidate.Runtime
