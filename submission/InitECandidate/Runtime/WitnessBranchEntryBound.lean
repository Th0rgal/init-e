import InitECandidate.Runtime.WitnessBranchPreludeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem runBounded_witness_unwind_branch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (indexBound : index.toNat < 16)
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    : RunBounded s witnessUnwindBranch (witnessBranchFinishCost length.toNat) := by
  change RunBounded s (witnessBranchAt 0) _
  rw [source_witness_branch_entry]
  apply RunBounded.decWord s (ofString "br") _ heap
  · simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,branchReadable,branchCell]
  let first := setVarHOLFinite (ofString "br") (.val (.word heap)) s
  have firstTop : first.locals.lookup (ofString "top")=some (.val (.word top)) := by
    simpa (config := {decide := true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTop
  have firstDomain : first.memaddrs (top+32#64) := indexReadable
  have firstCell : first.memory (top+32#64)=.word index := indexCell
  apply RunBounded.decWord first (ofString "i") _ index
  · simp [evalHOLExact,evalListHOLExact,firstTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,firstDomain,firstCell]
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) first
  have other (name : MlS) (notI : name ≠ ofString "i") (notBr : name ≠ ofString "br") :
      entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notI,Ne.symm notBr]
  exact runBounded_witness_branch_prelude entered array pointer length scratch frame top heap index ceiling inputLimit
    arrayReadable arrayCell ((other _ (by decide) (by decide)).trans atTop) result
    ((other _ (by decide) (by decide)).trans atResult) recordBeforeTable tableBeforeBranch
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) indexBound
    (by simp (config := {decide := true}) [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    heapBound (slice.after_frame s entered array 16 pointer length rfl rfl rfl) inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms runBounded_witness_unwind_branch
end InitECandidate.Runtime
