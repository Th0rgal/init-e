import InitECandidate.Runtime.WitnessBranchEntryNormalScope
import InitECandidate.Runtime.WitnessBranchChildPrefixProgress
import InitECandidate.Runtime.WitnessBranchLastChildPrefixProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem witness_branch_entry_more_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top heap index result : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (beforeLast : index.toNat < 15) (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessUnwindBranch = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word top)) ∧
      post.locals.lookup (ofString "slot") = some (.val (.word (index+1))) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (2#64))) ∧
      post.memory (top+32#64) = .word (index+1) ∧ post.globals = s.globals ∧
      16-(index+1).toNat < 16-index.toNat := by
  let first := setVarHOLFinite (ofString "br") (.val (.word heap)) s
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) first
  obtain ⟨output,bodyRun,memory,globals,locals⟩ := witness_branch_entry_normal_scope s post top heap index
    atTop branchReadable branchCell indexReadable indexCell run
  have other (name : MlS) (notI : name ≠ ofString "i") (notBr : name ≠ ofString "br") :
      entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notI,Ne.symm notBr]
  have facts := witness_branch_child_prefix_normal_progress entered output top heap index result
    ((other _ (by decide) (by decide)).trans atTop)
    (by simp (config := {decide := true}) [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((other _ (by decide) (by decide)).trans atResult)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) beforeLast code bodyRun
  exact ⟨(locals _ (by decide) (by decide)).trans facts.1,
    (locals _ (by decide) (by decide)).trans facts.2.1,
    (locals _ (by decide) (by decide)).trans facts.2.2.1,
    (congrFun memory _).trans facts.2.2.2.1, globals.trans facts.2.2.2.2.1, facts.2.2.2.2.2⟩

theorem witness_branch_entry_last_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap prev : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word (15#64))
    (prevCell : s.memory top = .word prev) (topAbove : ceiling ≤ top.toNat)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s witnessUnwindBranch = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
      post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
      post.memory top = s.memory top := by
  let first := setVarHOLFinite (ofString "br") (.val (.word heap)) s
  let entered := setVarHOLFinite (ofString "i") (.val (.word (15#64))) first
  obtain ⟨output,bodyRun,memory,globals,locals⟩ := witness_branch_entry_normal_scope s post top heap (15#64)
    atTop branchReadable branchCell indexReadable indexCell run
  have other (name : MlS) (notI : name ≠ ofString "i") (notBr : name ≠ ofString "br") :
      entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notI,Ne.symm notBr]
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_branch_last_child_prefix_normal_progress entered output
    array pointer length scratch frame top heap prev ceiling inputLimit arrayReadable arrayCell
    ((other _ (by decide) (by decide)).trans atTop) result
    ((other _ (by decide) (by decide)).trans atResult) recordBeforeTable tableBeforeBranch
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    prevCell topAbove before heapBound (slice.after_frame s entered array 16 pointer length rfl rfl rfl)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget bodyRun
  exact ⟨(locals _ (by decide) (by decide)).trans topPost,
    (locals _ (by decide) (by decide)).trans resultPost,
    ((locals _ (by decide) (by decide)).trans modePost).trans (other _ (by decide) (by decide)),
    (congrFun memory _).trans cellPost⟩
#print axioms witness_branch_entry_more_normal_progress
#print axioms witness_branch_entry_last_normal_progress
end InitECandidate.Runtime
