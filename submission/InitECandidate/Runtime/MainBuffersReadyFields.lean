import InitECandidate.Runtime.MainBuffersZeroFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execution-linked input/output bindings, heap geometry, and global frame
at the end of main's two buffer declarations. -/
theorem MainBuffersReady.fields {F : Type} {state ready : PanSemStateFiniteExact 64 F}
    (valid : MainBuffersReady state ready) :
    ∃ length out zero heap : BitVec 64,
      ready.locals.lookup (ofString "inp") =
        some (.rStruct [.val (.word 2713731432),.val (.word length)]) ∧
      ready.locals.lookup (ofString "out") = some (.val (.word out)) ∧
      ready.locals.lookup (ofString "z32") = some (.val (.word zero)) ∧
      length.toNat ≤ 134217712 ∧ 2713731432 + length.toNat < 2 ^ 64 ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0 ∧ 2713731432 ≤ heap.toNat ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      (∀ key, key ≠ ofString "heap_ptr" →
        ready.globals.lookup key = (allInitializerGlobals state.globals).lookup key) := by
  obtain ⟨inputState,pointer,inputReady,inputHeap,middle,outReady,zeroReady⟩ := valid
  obtain ⟨initialized,initializerReady,length,small,inputLocals,inputGlobals,_,inputCover,_,inputCode,inputDomain⟩ := inputReady
  obtain ⟨outLocals,_,outCode,outDomain,outGlobals,_,outCover,_⟩ := outReady
  obtain ⟨zeroLocals,_,zeroCode,zeroDomain,zeroGlobals,capped,zeroCover,aligned⟩ := zeroReady
  let zero := allocationEnd pointer 256
  let heap := allocationEnd zero 32
  have pointerEq : allocationEnd 2713731432 (length + 8) = pointer := by
    rw [inputGlobals] at inputHeap
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using inputHeap
  have inputLower : 2713731432 ≤ pointer.toNat := by
    rw [pointerEq] at inputCover
    change 2713731432 + length.toNat + 8 ≤ pointer.toNat at inputCover
    omega
  refine ⟨length,pointer,zero,heap,?_,?_,?_,small,(by omega),?_,capped,aligned,?_,
    zeroCode.trans (outCode.trans (inputCode.trans initializerReady.2.1)),
    zeroDomain.trans (outDomain.trans (inputDomain.trans initializerReady.2.2.1)),?_⟩
  · rw [zeroLocals,outLocals,inputLocals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · rw [zeroLocals,outLocals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · rw [zeroLocals]
    simp [zero,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [zeroGlobals]
    simp [heap,zero,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · change pointer.toNat + 256 ≤ zero.toNat at outCover
    change zero.toNat + 32 ≤ heap.toNat at zeroCover
    omega
  · intro key notHeap
    simp [zeroGlobals,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notHeap,outGlobals,inputGlobals,initializerReady.1]

#print axioms MainBuffersReady.fields
end InitECandidate.Runtime
