import InitECandidate.Runtime.WitnessUnwindConcreteBound
import InitECandidate.Runtime.WitnessUnwindExtensionBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_witness_unwind_nonzero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top : BitVec 64) (cost : Nat)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top))) (nonzero : top ≠ 0)
    (bounded : RunBounded s witnessUnwindNonempty cost) : RunBounded s decodeWitnessNodeUnwindMode cost := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=evaluateHOLFiniteState s witnessUnwindNonempty := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL,
      show top ≠ 0#64 from nonzero]
  unfold RunBounded at bounded ⊢
  rw [evaluation]
  exact bounded

theorem runBounded_witness_unwind_empty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word (0#64))))
    (code : s.code=originalRuntimeCode) : RunBounded s decodeWitnessNodeUnwindMode 0 := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=
      evaluateHOLFiniteState s (.assign .local (ofString "go") (.const 0)) := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL]
  have bounded : RunBounded s (.assign .local (ofString "go") (.const 0)) 0 :=
    RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega)
  unfold RunBounded at bounded ⊢
  rw [evaluation]
  exact bounded

theorem runBounded_witness_unwind_branch_mode {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index hash : BitVec 64) (ceiling inputLimit : Nat)
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
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (2#64))
    (resultAfterTable : result=0 ∨ array.toNat+272 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (nonzero : top ≠ 0)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    : RunBounded s decodeWitnessNodeUnwindMode (witnessBranchFinishCost length.toNat) := by
  apply runBounded_witness_unwind_nonzero s top _ atTop nonzero
  exact runBounded_witness_unwind_branch_nonempty s array pointer length scratch frame top heap index hash ceiling inputLimit
    arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell indexReadable indexCell
    indexBound heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena hashReadable hashCell stageReadable stageCell resultAfterTable resultBound budget

theorem runBounded_witness_unwind_extension_mode {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top result hash : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (nonzero : top ≠ 0)
    (code : s.code=originalRuntimeCode) (budget : 5 ≤ s.clock) :
    RunBounded s decodeWitnessNodeUnwindMode 5 := by
  apply runBounded_witness_unwind_nonzero s top 5 atTop nonzero
  exact runBounded_witness_unwind_extension_nonempty s top result hash atTop atResult hashReadable hashCell stageReadable stageCell
    topBound resultAfterRecord resultBound code budget

theorem witness_branch_finish_cost_mono {n m : Nat} (bound : n ≤ m) :
    witnessBranchFinishCost n ≤ witnessBranchFinishCost m := by
  have product : n*((2*n+1)*15+19) ≤ m*((2*m+1)*15+19) := Nat.mul_le_mul bound (by omega)
  unfold witnessBranchFinishCost
  omega

theorem witness_branch_finish_cost_covers_extension (n : Nat) : 5 ≤ witnessBranchFinishCost n := by
  unfold witnessBranchFinishCost
  omega

#print axioms witness_branch_finish_cost_mono
#print axioms witness_branch_finish_cost_covers_extension
#print axioms runBounded_witness_unwind_nonzero
#print axioms runBounded_witness_unwind_empty
#print axioms runBounded_witness_unwind_branch_mode
#print axioms runBounded_witness_unwind_extension_mode
end InitECandidate.Runtime
