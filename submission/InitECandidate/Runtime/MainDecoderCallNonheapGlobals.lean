import InitECandidate.Runtime.MainDecoderCallReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The handled main decoder call retains all non-heap globals, including the
actual SHA and SSZ workspace pointers installed by initialization. -/
theorem main_decoder_call_nonheap_globals {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = ready.globals.lookup key := by
  obtain ⟨length,heap,binding,small,input,locals,returned,geometry⟩ :=
    main_decoder_call_returned_heap state ready post code arena valid run
  exact returned.2.1.2

#print axioms main_decoder_call_nonheap_globals
end InitECandidate.Runtime
