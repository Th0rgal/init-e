import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.AllocationDeclarationReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful main executions expose the two actual output allocations and
retain the input pair. Failed allocations cannot manufacture this return. -/
theorem main_buffers_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer input length : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 33806089496)
    (inp : state.locals.lookup (ofString "inp") =
      some (.rStruct [.val (.word input),.val (.word length)]))
    (inputBefore : input.toNat + length.toNat ≤ pointer.toNat)
    (run : evaluateHOLFiniteState state (mainAt 15) = (some (.returned value),post)) :
    ∃ (ready output : PanSemStateFiniteExact 64 F) (zero nextHeap : BitVec 64),
      evaluateHOLFiniteState ready (mainAt 17) = (some (.returned value),output) ∧
      ready.locals.lookup (ofString "inp") = some (.rStruct [.val (.word input),.val (.word length)]) ∧
      ready.locals.lookup (ofString "out") = some (.val (.word pointer)) ∧
      ready.locals.lookup (ofString "z32") = some (.val (.word zero)) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      zero.toNat % 8 = 0 ∧ pointer.toNat + 256 ≤ zero.toNat ∧
      zero.toNat + 32 ≤ nextHeap.toNat ∧ input.toNat + length.toNat ≤ nextHeap.toNat ∧
      ready.memory = state.memory ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  rw [source_main_output_declaration] at run
  have args256 : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const 256] = some [.val (.word 256)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  obtain ⟨middle,midOutput,midRun,midLocals,midMemory,midCode,midDomain,midGlobals,midBound,midCover,midAligned,
      postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned state post (ofString "out")
    (.const 256) (mainAt 16) pointer 256 value args256 code heap bounded run
  let zero := allocationEnd pointer 256
  have midHeap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word zero)) := by
    rw [midGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,zero]
  rw [source_main_zero_declaration] at midRun
  have args32 : evalListHOLFinite middle (h := fun a => Classical.propDecidable (middle.memaddrs a))
      [.const 32] = some [.val (.word 32)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  obtain ⟨ready,output,tail,locals,memory,installed,domain,globals,within,cover,aligned,tailMemory,tailGlobals,tailDomain⟩ :=
    allocation_declaration_returned middle midOutput (ofString "z32") (.const 32) (mainAt 17) zero 32 value
      args32 (midCode.trans code) midHeap midBound midRun
  have inpOut : ofString "out" ≠ ofString "inp" := by decide
  have inpZero : ofString "z32" ≠ ofString "inp" := by decide
  have outZero : ofString "z32" ≠ ofString "out" := by decide
  refine ⟨ready,output,zero,allocationEnd zero 32,tail,?_,?_,?_,?_,within,aligned,midAligned,?_,?_,?_,
    memory.trans midMemory,installed.trans midCode,domain.trans midDomain,?_,
    postMemory.trans tailMemory,postGlobals.trans tailGlobals,postDomain.trans tailDomain⟩
  · simp [locals,midLocals,HolFiniteMapExact.lookup_update,FUPDATE,inpOut,inpZero,inp]
  · simp [locals,midLocals,HolFiniteMapExact.lookup_update,FUPDATE,outZero]
  · simp [locals,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · change pointer.toNat + 256 ≤ (allocationEnd pointer 256).toNat
    simpa using midCover
  · simpa using cover
  · have c1 : pointer.toNat + 256 ≤ zero.toNat := by simpa [zero] using midCover
    have c2 : zero.toNat + 32 ≤ (allocationEnd zero 32).toNat := by simpa using cover
    omega
  · intro key different
    rw [globals]
    simp only [setGlobalHOLFinite]
    rw [midGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms main_buffers_returned
end InitECandidate.Runtime
