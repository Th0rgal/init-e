import InitECandidate.Runtime.WitnessBranchPreludeMemoryFrame
import InitECandidate.Runtime.WitnessBranchEntryNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_branch_entry_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (indexBound : index.toNat<16) (heapBound : heap.toNat ≤ 33806089496)
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
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat →
      watched≠top+32 → watched≠top+40 → post.memory watched=s.memory watched := by
  let first := setVarHOLFinite (ofString "br") (.val (.word heap)) s
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) first
  obtain ⟨output,bodyRun,memory,globals,locals⟩ := witness_branch_entry_normal_scope s post top heap index
    atTop branchReadable branchCell indexReadable indexCell run
  have other (name : MlS) (notI : name≠ofString "i") (notBr : name≠ofString "br") : entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notI,Ne.symm notBr]
  obtain ⟨scratchPost,framePost,heapPost,bodyMemory⟩ := witness_branch_prelude_normal_memory_frame entered output
    array pointer length scratch frame top heap index ceiling inputLimit arrayReadable arrayCell
    ((other _ (by decide) (by decide)).trans atTop) result ((other _ (by decide) (by decide)).trans atResult)
    recordBeforeTable tableBeforeBranch
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    indexBound heapBound (slice.after_frame s entered array 16 pointer length rfl rfl rfl)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget bodyRun
  refine ⟨?_,?_,?_,?_⟩
  · rw [globals];exact scratchPost
  · rw [globals];exact framePost
  · rw [globals];exact heapPost
  · intro watched above below notIndex notOcc
    exact (congrFun memory watched).trans (bodyMemory watched above below notIndex notOcc)

#print axioms witness_branch_entry_normal_memory_frame
end InitECandidate.Runtime
