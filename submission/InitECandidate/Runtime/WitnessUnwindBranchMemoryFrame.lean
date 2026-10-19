import InitECandidate.Runtime.WitnessUnwindNormalPrefix
import InitECandidate.Runtime.WitnessBranchEntryMemoryFrame
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_branch_nonempty_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState s witnessUnwindNonempty=(none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat →
      watched≠top+32 → watched≠top+40 → result=0 ∨ watched≠result+24 → post.memory watched=s.memory watched := by
  obtain ⟨next,output,tailRun,locals,globals,codeEq,domain,endian,clock,memory,postMemory,postGlobals,postLocals⟩ :=
    witness_unwind_nonempty_normal_prefix s post top result hash atTop atResult hashReadable hashCell code run
  have other (name : MlS) (different : name ≠ ofString "hash") : next.locals.lookup name=s.locals.lookup name := by
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have nextTop := (other _ (by decide)).trans atTop
  have nextResult := (other _ (by decide)).trans atResult
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
    apply memory watched
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
      show next.memaddrs (top+8#64) from by rw [domain]; exact stageReadable,
      stageKept,stageCell,Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_ite,condition] at tailRun
  change evaluateHOLFiniteState next witnessUnwindBranch=(none,output) at tailRun
  obtain ⟨scratchPost,framePost,heapPost,branchMemory⟩ := witness_branch_entry_normal_memory_frame next output
    array pointer length scratch frame top heap index ceiling inputLimit
    (by rw [domain];exact arrayReadable) (arrayKept.trans arrayCell) nextTop result nextResult
    recordBeforeTable tableBeforeBranch
    (by rw [domain];exact branchReadable) (branchKept.trans branchCell)
    (by rw [domain];exact indexReadable) (indexKept.trans indexCell) indexBound heapBound
    (slice.after_frame s next array 16 pointer length domain ptrKept lenKept)
    inputRange lengthBound limitBound (by rw [globals];exact scratchGlobal) (by rw [globals];exact frameGlobal)
    (codeEq.trans code) orderedFrame framePositive scratchBelow
    (by intro address lower upper;rw [domain];exact arena address lower upper) (by rw [clock];exact budget) tailRun
  refine ⟨?_,?_,?_,?_⟩
  · rw [postGlobals];exact scratchPost
  · rw [postGlobals];exact framePost
  · rw [postGlobals];exact heapPost.trans (by rw [globals])
  · intro watched above below notIndex notOcc separate
    exact (congrFun postMemory watched).trans ((branchMemory watched above below notIndex notOcc).trans (memory watched separate))

#print axioms witness_unwind_branch_nonempty_memory_frame
end InitECandidate.Runtime
