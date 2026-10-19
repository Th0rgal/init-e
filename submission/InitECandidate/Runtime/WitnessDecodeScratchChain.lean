import InitECandidate.Runtime.WitnessScratchChainHeadFrame
import InitECandidate.Runtime.WitnessDecodeModeHeapFrame
import InitECandidate.Runtime.WitnessDecodeModePushedMetadata
import InitECandidate.Runtime.WitnessDecodeModeWorkspace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_decode_mode_normal_scratch_chain {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array previous : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word previous)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atPointer : s.locals.lookup (ofString "cur_p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "cur_n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit + 1 ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712)
    (upper : Nat) (ceilingBelowUpper : ceiling≤upper) (upperBeforeHeap : upper≤array.toNat)
    (chain : WitnessScratchChain s upper ceiling previous)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode=(none,post)) :
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    ((post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
      post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
      post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
      WitnessScratchChain post upper scratch.toNat previous) ∨
    ∃ record : BitVec 64,
      post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧
      post.locals.lookup (ofString "top")=some (.val (.word record)) ∧
      post.globals.lookup (ofString "scratch_ptr")=some (.val (.word record)) ∧
      record=scratchAllocationEnd scratch 88 ∧ frame.toNat≤record.toNat ∧ record.toNat+88≤scratch.toNat ∧
      WitnessScratchChain post upper record.toNat record) := by
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memory⟩ := witness_decode_mode_normal_heap_frame s post
    table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  have oldChain := chain.after_frame s post previous upper ceiling scratch.toNat scratchBelow
    (by intro watched above below;exact memory watched above (by omega))
  have metadata := witness_decode_mode_normal_pushed_metadata s post table pointer length scratch frame array previous ceiling inputLimit
    atTop atTable atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  obtain ⟨framePost,shape⟩ := witness_decode_mode_normal_workspace_shape s post table pointer length scratch frame array ceiling inputLimit
    atTable atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  refine ⟨framePost,?_⟩
  rcases metadata with ⟨mode,top⟩ | ⟨record,top,mode,identity,afterFrame,beforeScratch,accessible,tableData,link⟩
  · rcases shape with ⟨scratchPost,_,_,_⟩ | ⟨record,_,_,_,_,_,_,modeTwo,_⟩
    · exact Or.inl ⟨mode,top.trans atTop,scratchPost,oldChain⟩
    · have bad : (0#64)=(2#64) := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (mode.symm.trans modeTwo)))
      cases bad
  · rcases shape with ⟨_,_,_,modeZero⟩ | ⟨shapeRecord,shapeIdentity,scratchPost,_,_,_,_,_,_⟩
    · have bad : (0#64)=(2#64) := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (modeZero.symm.trans mode)))
      cases bad
    · have same : shapeRecord=record := shapeIdentity.trans identity.symm
      subst shapeRecord
      exact Or.inr ⟨record,mode,top,(by simpa only [identity] using scratchPost),identity,afterFrame,beforeScratch,
        oldChain.push post record previous upper scratch.toNat record.toNat (by omega) beforeScratch
          (by omega) (Nat.le_refl _) link⟩

#print axioms witness_decode_mode_normal_scratch_chain
end InitECandidate.Runtime
