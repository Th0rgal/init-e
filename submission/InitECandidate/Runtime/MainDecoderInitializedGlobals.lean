import InitECandidate.Runtime.MainDecoderCallNonheapGlobals
import InitECandidate.Runtime.MainBuffersReadyFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem MainDecoderEntry.initialized_nonheap {F : Type}
    {state ready : PanSemStateFiniteExact 64 F} (valid : MainDecoderEntry state ready)
    (key : MlS) (different : key≠ofString "heap_ptr") :
    ready.globals.lookup key=(allInitializerGlobals state.globals).lookup key := by
  obtain ⟨buffers,_,bufferValid,_,_,globals,_,_⟩ := valid
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,other⟩ := bufferValid.fields
  rw [globals]
  exact other key different

/-- Actual decoding retains every non-heap initializer global. -/
theorem main_decoder_call_initialized_nonheap {F : Type}
    (state ready post : PanSemStateFiniteExact 64 F) (code : state.code=originalRuntimeCode)
    (arena : ∀address : BitVec 64,address.toNat%8=0→2713714688≤address.toNat→
      address.toNat<33806089496→state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall=(none,post))
    (key : MlS) (different : key≠ofString "heap_ptr") :
    post.globals.lookup key=(allInitializerGlobals state.globals).lookup key :=
  (main_decoder_call_nonheap_globals state ready post code arena valid run key different).trans
    (valid.initialized_nonheap key different)

#print axioms MainDecoderEntry.initialized_nonheap
#print axioms main_decoder_call_initialized_nonheap
end InitECandidate.Runtime
