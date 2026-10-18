import InitECandidate.Runtime.MainInitializationBuffersReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real allocation chain supplies the aligned zero-buffer interval
and preserves the original code and word-cell domain. -/
theorem MainBuffersReady.zero_fields {F : Type} {state ready : PanSemStateFiniteExact 64 F}
    (valid : MainBuffersReady state ready) :
    ∃ zero : BitVec 64,
      ready.locals.lookup (ofString "z32") = some (.val (.word zero)) ∧
      zero.toNat % 8 = 0 ∧ 2713714688 ≤ zero.toNat ∧ zero.toNat + 32 ≤ 33806089496 ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs := by
  obtain ⟨inputState,pointer,inputReady,inputHeap,middle,outReady,zeroReady⟩ := valid
  obtain ⟨initialized,initializerReady,length,_,_,inputGlobals,_,inputCover,_,inputCode,inputDomain⟩ := inputReady
  obtain ⟨_,_,outCode,outDomain,_,_,outCover,outAligned⟩ := outReady
  obtain ⟨zeroLocals,_,zeroCode,zeroDomain,_,zeroCapped,zeroCover,_⟩ := zeroReady
  have pointerEq : allocationEnd 2713731432 (length + 8) = pointer := by
    rw [inputGlobals] at inputHeap
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using inputHeap
  have inputLower : 2713731432 ≤ pointer.toNat := by
    rw [pointerEq] at inputCover
    change 2713731432 + length.toNat + 8 ≤ pointer.toNat at inputCover
    omega
  refine ⟨allocationEnd pointer 256,?_,outAligned,?_,?_,
    zeroCode.trans (outCode.trans (inputCode.trans initializerReady.2.1)),
    zeroDomain.trans (outDomain.trans (inputDomain.trans initializerReady.2.2.1))⟩
  · rw [zeroLocals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · change pointer.toNat + 256 ≤ (allocationEnd pointer 256).toNat at outCover
    omega
  · change (allocationEnd pointer 256).toNat + 32 ≤
      (allocationEnd (allocationEnd pointer 256) 32).toNat at zeroCover
    omega

#print axioms MainBuffersReady.zero_fields
end InitECandidate.Runtime
