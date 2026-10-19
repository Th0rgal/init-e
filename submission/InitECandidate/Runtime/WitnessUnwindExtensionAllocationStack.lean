import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
import InitECandidate.Runtime.WitnessAllocationStackPop
import InitECandidate.Runtime.WitnessTraversalChildCredit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual extension unwind retains the saved parent allocation order, delivers
its real freshly allocated node above those parents, and decreases the measure. -/
theorem witness_unwind_extension_allocation_stack {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength top previous child hash heap frame : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength heap persistentFloor lower top)
    (childAbove : WitnessResultAboveStack s input inputLength top child persistentFloor lower)
    (childBound : child.toNat≤heap.toNat)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word child)))
    (atMode : s.locals.lookup (ofString "mode")=some (.val (.word (0#64))))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (prevCell : s.memory top=.word previous)
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (code : s.code=originalRuntimeCode) (nonempty : top≠0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
      post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 56))) ∧
      WitnessAllocationStack post input inputLength (allocationEnd heap 56) persistentFloor lower previous ∧
      WitnessResultAboveStack post input inputLength previous heap persistentFloor lower ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) previous (witnessTraversalChildCredit post previous) 1 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 1 := by
  have recordBeforeHeap : top.toNat+88≤heap.toNat := by
    cases stack with
    | nil => exact False.elim (nonempty rfl)
    | cons parent above valid floorBound parentBound ordered branchAbove tail =>
      have before := valid.2.1
      omega
  have resultAfterRecord := childAbove.record_geometry s input inputLength top child persistentFloor lower nonempty
  have resultBound : child.toNat≤33806089496 := childBound.trans heapBound
  obtain ⟨heapPost,growth,capped,aligned,scratchPost,framePost,memory⟩ := witness_unwind_extension_mode_heap_frame
    s post top child hash heap atTop atResult hashReadable hashCell stageReadable stageCell atHeap heapBound
    (by omega) resultAfterRecord resultBound code nonempty run
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_unwind_extension_mode_normal_progress
    s post top child hash heap previous atTop atResult hashReadable hashCell stageReadable stageCell prevCell atHeap
    (by omega) heapBound (by omega) resultAfterRecord resultBound code nonempty run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeUnwindMode
  rw [run] at metadata
  have child24Nat : (child+(24 : BitVec 64)).toNat=child.toNat+24 := by
    rw [BitVec.toNat_add]
    change (child.toNat+24)%2^64=child.toNat+24
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨parentStack,parentResult⟩ := stack.extension_pop_after_result_hash_frame s post input inputLength heap
    (allocationEnd heap 56) top previous child heap persistentFloor lower childAbove childBound nonempty prevCell
    growth (Nat.le_refl _) metadata.2.1 (by
      intro watched afterRecord beforeHeap safe
      apply memory watched beforeHeap
      rcases safe with zero | beforeChild
      · exact Or.inl zero
      · apply Or.inr
        intro same
        have equal := congrArg BitVec.toNat same
        rw [child24Nat] at equal
        omega)
  have capacity : decoderScratchCapacity frame post=decoderScratchCapacity frame s := by
    unfold decoderScratchCapacity
    rw [scratchPost]
  have measure := (stack.physical s input inputLength heap top persistentFloor lower).pop_measure s
    input inputLength heap top previous persistentFloor lower (decoderScratchCapacity frame s)
    (witnessTraversalChildCredit s top) (witnessTraversalChildCredit post previous) 1 1 nonempty prevCell
    (witnessTraversalChildCredit_bound post previous) (by decide)
  refine ⟨topPost,resultPost,modePost.trans atMode,heapPost,parentStack,parentResult,?_⟩
  rw [capacity]
  exact measure

#print axioms witness_unwind_extension_allocation_stack
end InitECandidate.Runtime
