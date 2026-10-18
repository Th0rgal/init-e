import InitECandidate.Runtime.SszSplitVarListDeclarationReturned
import InitECandidate.Runtime.SszSplitVarListReturnedInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned list declaration enters its real continuation with readable
input-bounded slices and a capped aligned heap beyond the array. -/
theorem sszSplitVarList_declaration_array_origin {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (arguments : List (ExpHOL 64))
    (pointer length limit heapPointer : BitVec 64) (finalValue : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length),.val (.word limit)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (run : evaluateHOLFiniteState state
      (.decCall name (.comb [.one,.one]) (ofString "ssz_split_var_list") arguments continuation) =
      (some (.returned finalValue),post)) :
    ∃ (array count nextHeap : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState ready continuation = (some (.returned finalValue),output) ∧
      ready.locals = state.locals.update (name,.rStruct [.val (.word array),.val (.word count)]) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      RlpSliceInputPrefix ready array pointer length count.toNat ∧ count.toNat ≤ length.toNat / 4 ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧ heapPointer.toNat ≤ nextHeap.toNat ∧
      array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧ (count = 0 ∨ array = heapPointer) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  obtain ⟨value,bodyPost,output,bodyRun,body,slices,tail,postMemory,postGlobals,postDomain⟩ :=
    sszSplitVarList_declaration_returned state post name continuation arguments pointer length limit heapPointer finalValue
      args code heap heapBound run
  let entry := callEntryStateHOLFinite state (sszSplitCalleeLocals pointer length limit)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
  rw [bodyRun] at metadata
  obtain ⟨array,count,nextHeap,returned,inputPrefix,countBound,nextGlobal,nextBound,nextAligned,growth,arrayBefore⟩ :=
    sszSplitVarList_returned_input_prefix entry bodyPost pointer length limit heapPointer value heap heapBound aligned
      metadata.2.1 inputFits body slices
  have origin : count = 0 ∨ array = heapPointer := by
    rcases body with ⟨_,pair,_⟩ | ⟨_,first,_,_,pair,_⟩
    · have equal := returned.symm.trans pair
      simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true] at equal
      exact Or.inl equal.2
    · have equal := returned.symm.trans pair
      simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true] at equal
      exact Or.inr equal.1
  rw [returned] at tail
  let ready := setVarHOLFinite name (.rStruct [.val (.word array),.val (.word count)]) {bodyPost with locals := state.locals}
  have readyPrefix : RlpSliceInputPrefix ready array pointer length count.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := inputPrefix index inside
    exact ⟨p,n,item.after_frame bodyPost ready array index p n pointer length rfl rfl rfl⟩
  exact ⟨array,count,nextHeap,ready,output,tail,rfl,metadata.1,metadata.2.1,readyPrefix,countBound,
    nextGlobal,nextBound,nextAligned,growth,arrayBefore,origin,postMemory,postGlobals,postDomain⟩

#print axioms sszSplitVarList_declaration_array_origin
end InitECandidate.Runtime
