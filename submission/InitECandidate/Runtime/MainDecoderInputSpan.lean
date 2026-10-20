import InitECandidate.Runtime.MainDecoderEntryFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem MainBuffersReady.input_before_heap {F : Type} {state ready : PanSemStateFiniteExact 64 F}
    (valid : MainBuffersReady state ready) (length heap : BitVec 64)
    (input : ready.locals.lookup (ofString "inp")=some (.rStruct [.val (.word 2713731432),.val (.word length)]))
    (binding : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    2713731432+length.toNat≤heap.toNat := by
  obtain ⟨inputState,pointer,inputReady,inputHeap,middle,outReady,zeroReady⟩ := valid
  obtain ⟨initialized,initializerReady,actualLength,small,inputLocals,inputGlobals,_,inputCover,rest⟩ := inputReady
  obtain ⟨outLocals,_,_,_,_,_,outCover,_⟩ := outReady
  obtain ⟨zeroLocals,_,_,_,zeroGlobals,_,zeroCover,_⟩ := zeroReady
  have actualInput : ready.locals.lookup (ofString "inp")=
      some (.rStruct [.val (.word 2713731432),.val (.word actualLength)]) := by
    rw [zeroLocals,outLocals,inputLocals]
    simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  have sameLength : length=actualLength := by
    have same := input.symm.trans actualInput
    simpa only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,
      ValueHOL.val.injEq,HolWordLab.word.injEq,true_and,and_true] using same
  subst actualLength
  have pointerEq : allocationEnd 2713731432 (length+8)=pointer := by
    rw [inputGlobals] at inputHeap
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using inputHeap
  have heapEq : heap=allocationEnd (allocationEnd pointer 256) 32 := by
    rw [zeroGlobals] at binding
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using binding.symm
  rw [pointerEq] at inputCover
  change 2713731432+length.toNat+8≤pointer.toNat at inputCover
  change pointer.toNat+256≤(allocationEnd pointer 256).toNat at outCover
  change (allocationEnd pointer 256).toNat+32≤(allocationEnd (allocationEnd pointer 256) 32).toNat at zeroCover
  rw [heapEq]
  omega

theorem MainDecoderEntry.input_before_heap {F : Type} {state ready : PanSemStateFiniteExact 64 F}
    (valid : MainDecoderEntry state ready) (length heap : BitVec 64)
    (input : ready.locals.lookup (ofString "inp")=some (.rStruct [.val (.word 2713731432),.val (.word length)]))
    (binding : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    2713731432+length.toNat≤heap.toNat := by
  obtain ⟨buffers,_,bufferValid,_,locals,globals,_,_⟩ := valid
  apply bufferValid.input_before_heap length heap
  · rw [locals] at input
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using input
  · rw [globals] at binding
    exact binding

#print axioms MainBuffersReady.input_before_heap
#print axioms MainDecoderEntry.input_before_heap
end InitECandidate.Runtime
