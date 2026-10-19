import InitECandidate.Runtime.WitnessBranchEntryBound
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.WitnessUnwindPrefixFrame
import InitECandidate.Runtime.WitnessExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem runBounded_witness_unwind_branch_nonempty {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    : RunBounded s witnessUnwindNonempty (witnessBranchFinishCost length.toNat) := by
  rw [source_witness_unwind_nonempty]
  apply RunBounded.decWord s (ofString "hash") _ hash
  · simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,hashReadable,hashCell]
  let entered := setVarHOLFinite (ofString "hash") (.val (.word hash)) s
  have other (name : MlS) (different : name ≠ ofString "hash") : entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atHash : entered.locals.lookup (ofString "hash")=some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTopEntered := (other _ (by decide)).trans atTop
  have atResultEntered := (other _ (by decide)).trans atResult
  have enteredBudget : witnessBranchFinishCost length.toNat ≤ entered.clock := budget
  have whole := RunBounded.seq (tail := .ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))
      witnessUnwindExtension witnessUnwindBranch) (b := witnessBranchFinishCost length.toNat)
    (RunBounded.ofProg (state := entered) witness_unwind_hash_store_bounded code (by omega))
    (by simpa only [Nat.zero_add] using enteredBudget) (by
      intro next normal nextCode ticks
      have frames := witness_unwind_hash_store_frame entered result hash atHash atResultEntered code
      have metadata := evaluateHOLFiniteState_metadata entered witnessUnwindHashStore
      rw [normal] at frames metadata
      have nextTop : next.locals.lookup (ofString "top")=some (.val (.word top)) := by
        rw [frames.1]; exact atTopEntered
      have nextResult : next.locals.lookup (ofString "result")=some (.val (.word result)) := by
        rw [frames.1]; exact atResultEntered
      have addNat (base : BitVec 64) (offset : Nat) (small : base.toNat+offset < 2^64) :
          (base+BitVec.ofNat 64 offset).toNat=base.toNat+offset := by
        rw [BitVec.toNat_add,BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : offset < 2^64),Nat.mod_eq_of_lt small]
      have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
        rw [BitVec.toNat_add]
        change (result.toNat+24)%2^64=result.toNat+24
        exact Nat.mod_eq_of_lt (by omega)
      have kept (watched : BitVec 64) (below : watched.toNat < array.toNat+272) :
          next.memory watched=s.memory watched := by
        apply frames.2.2 watched
        rcases resultAfterTable with zero | lower
        · exact Or.inl zero
        · apply Or.inr
          intro same
          have equal := congrArg BitVec.toNat same
          rw [resultNat] at equal
          omega
      have topNat (offset : Nat) (inside : offset < 88) :
          (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := addNat top offset (by omega)
      have stageKept := kept (top+8#64) (by rw [topNat 8 (by decide)]; omega)
      have arrayKept := kept (top+24#64) (by rw [topNat 24 (by decide)]; omega)
      have branchKept := kept (top+16#64) (by rw [topNat 16 (by decide)]; omega)
      have indexKept := kept (top+32#64) (by rw [topNat 32 (by decide)]; omega)
      have pointerNat := rlpSlice_cell_toNat array (16#64) (17#64) 0 (by decide) (by decide)
        (by change array.toNat+17*16 ≤ 2^64; omega)
      have lengthNat := rlpSlice_cell_toNat array (16#64) (17#64) 8 (by decide) (by decide)
        (by change array.toNat+17*16 ≤ 2^64; omega)
      have ptrKept := kept (array+(16#64)*16#64) (by simpa only [BitVec.add_zero,Nat.add_zero] using (show (array+(16#64)*16#64+0#64).toNat < array.toNat+272 from by rw [pointerNat]; change array.toNat+256 < array.toNat+272; omega))
      have lenKept := kept (array+(16#64)*16#64+8#64) (by rw [lengthNat]; change array.toNat+264 < array.toNat+272; omega)
      have condition : @evalHOLExact 64 F _ next.toExact (fun a => Classical.propDecidable (next.memaddrs a))
          (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))=
          some (.val (.word (0#64))) := by
        simp [evalHOLExact,evalListHOLExact,nextTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
          memLoadHOLExact,
          show next.memaddrs (top+8#64) from by rw [metadata.2.1]; exact stageReadable,
          stageKept,stageCell,Compiler.Encoders.Asm.wordCmpHOL]
      unfold RunBounded
      rw [evaluateHOLFiniteState_ite,condition]
      change RunBounded next witnessUnwindBranch _
      exact runBounded_witness_unwind_branch next array pointer length scratch frame top heap index ceiling inputLimit
        (by rw [metadata.2.1]; exact arrayReadable) (arrayKept.trans arrayCell) nextTop result nextResult recordBeforeTable tableBeforeBranch
        (by rw [metadata.2.1]; exact branchReadable) (branchKept.trans branchCell)
        (by rw [metadata.2.1]; exact indexReadable) (indexKept.trans indexCell) indexBound heapBound
        (slice.after_frame s next array 16 pointer length metadata.2.1 ptrKept lenKept) inputRange lengthBound limitBound
        (by rw [frames.2.1]; exact scratchGlobal) (by rw [frames.2.1]; exact frameGlobal) (metadata.1.trans code)
        orderedFrame framePositive scratchBelow (by intro address lower upper; rw [metadata.2.1]; exact arena address lower upper) ticks)
  simpa using whole

#print axioms runBounded_witness_unwind_branch_nonempty
end InitECandidate.Runtime
