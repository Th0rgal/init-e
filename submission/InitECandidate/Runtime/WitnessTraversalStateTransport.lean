import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessDecodeModeSource
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Concrete next-state components rebuild the invariant while fixed input,
layout and arena obligations transfer through unchanged memory domain/code. -/
theorem WitnessTraversalState.after_components {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go nextScratch nextHeap nextTop nextMode nextGo : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go)
    (domain : post.memaddrs=s.memaddrs) (code : post.code=s.code)
    (atDb : post.locals.lookup (ofString "db")=some (.val (.word layout.table)))
    (atGo : post.locals.lookup (ofString "go")=some (.val (.word nextGo)))
    (atTop : post.locals.lookup (ofString "top")=some (.val (.word nextTop)))
    (atMode : post.locals.lookup (ofString "mode")=some (.val (.word nextMode)))
    (atScratch : post.globals.lookup (ofString "scratch_ptr")=some (.val (.word nextScratch)))
    (atFrame : post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word layout.frame)))
    (atHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)))
    (scratchLower : layout.frame.toNat≤nextScratch.toNat) (scratchBound : nextScratch.toNat≤layout.scratchUpper)
    (scratchAligned : nextScratch.toNat%8=0)
    (heapGrowth : heap.toNat≤nextHeap.toNat) (heapBound : nextHeap.toNat≤33806089496) (heapAligned : nextHeap.toNat%8=0)
    (built : NodedbTableAt post layout.table layout.dbHeap layout.total)
    (entries : HashTableValuesIn layout.table (NodedbSliceTargets layout.dbArray layout.total) post)
    (slices : RlpSliceInputPrefix post layout.dbArray layout.input layout.inputLength layout.total.toNat)
    (stack : WitnessAllocationStack post layout.input layout.inputLength nextHeap layout.persistentFloor nextScratch.toNat nextTop)
    (scratchChain : WitnessScratchChain post layout.scratchUpper nextScratch.toNat nextTop)
    (goBits : nextGo=0 ∨ nextGo=1)
    (modes : nextMode=0 ∨ nextMode=1 ∨ nextMode=2)
    (decodeInput : nextMode=1 → ∃ pointer length : BitVec 64,
      post.locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
      post.locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
      layout.input.toNat≤pointer.toNat ∧ pointer.toNat+length.toNat≤layout.input.toNat+layout.inputLength.toNat ∧
      pointer.toNat+length.toNat<2^64 ∧ length.toNat≤layout.inputLength.toNat)
    (resolveSelector : nextMode=2 → nextTop≠0 ∧ WitnessSelectedSlot post nextTop)
    (delivered : nextMode=0 → ∃ node : BitVec 64,
      post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
      (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat)) ∧
      WitnessResultAboveStack post layout.input layout.inputLength nextTop node layout.persistentFloor nextScratch.toNat) :
    WitnessTraversalState layout post nextScratch nextHeap nextTop nextMode nextGo := by
  exact {
    code := code.trans valid.code, atDb := atDb, atTop := atTop, atMode := atMode, atGo := atGo,
    atScratch := atScratch, atFrame := atFrame, atHeap := atHeap,
    framePositive := valid.framePositive, scratchLower := scratchLower, scratchBound := scratchBound, scratchAligned := scratchAligned,
    scratchBeforeDatabase := valid.scratchBeforeDatabase, databaseBeforeFloor := valid.databaseBeforeFloor,
    floorBeforeHeap := valid.floorBeforeHeap.trans heapGrowth, heapBound := heapBound, heapAligned := heapAligned,
    inputRange := valid.inputRange, inputBound := valid.inputBound, inputLimitBound := valid.inputLimitBound,
    inputBeforeFrame := valid.inputBeforeFrame
    inputBeforeFloor := valid.inputBeforeFloor,
    scratchArena := by intro address lo hi;rw [domain];exact valid.scratchArena address lo hi,
    heapArena := by intro address lo hi;rw [domain];exact valid.heapArena address lo hi,
    built := built, entries := entries, slices := slices, tableAboveDatabase := valid.tableAboveDatabase,
    arrayAboveDatabase := valid.arrayAboveDatabase, dbHeapBeforeFloor := valid.dbHeapBeforeFloor, dbArrayEnd := valid.dbArrayEnd,
    stack := stack, scratchChain := scratchChain, modes := modes, goBits := goBits,
    decodeInput := decodeInput, resolveSelector := resolveSelector, delivered := delivered }

 theorem witness_decode_mode_normal_db_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode=(none,post)) :
    post.locals.lookup (ofString "db")=s.locals.lookup (ofString "db") := by
  have supported : avoidsLocal (ofString "db") decodeWitnessNodeDecodeMode=true := by
    rw [source_witness_decode_call,source_witness_decode_tail,source_witness_decode_completed,source_witness_decode_push]
    decide
  have kept := evaluate_avoidsLocal_flowing (ofString "db") decodeWitnessNodeDecodeMode supported s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
#print axioms WitnessTraversalState.after_components
#print axioms witness_decode_mode_normal_db_kept
end InitECandidate.Runtime
