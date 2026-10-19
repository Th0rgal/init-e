import InitECandidate.Runtime.MainDecoderCallNonheapGlobals
import InitECandidate.Runtime.AllInitializerHashWorkspace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal decoder call at main's actual entry retains the concrete workspace
pointers, without adding assumptions about their values to the main proof. -/
theorem main_decoder_hash_workspace_globals {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    post.globals.lookup (ofString "sha_st") = some (.val (.word 2713714688)) ∧
    post.globals.lookup (ofString "sha_accel") = some (.val (.word 2713714880)) ∧
    post.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word 2713715312)) ∧
    post.globals.lookup (ofString "zero_hashes") = some (.val (.word 2713715408)) := by
  have kept := main_decoder_call_nonheap_globals state ready post code arena valid run
  obtain ⟨buffers,_,bufferValid,_,locals,globals,installed,domain⟩ := valid
  obtain ⟨length,out,zero,heap,inp,output,z32,small,fits,atHeap,capped,aligned,lower,bufferCode,addresses,other⟩ :=
    bufferValid.fields
  have all (key : MlS) (ne : key ≠ ofString "heap_ptr") :
      post.globals.lookup key = (allInitializerGlobals state.globals).lookup key := by
    rw [kept key ne,globals,other key ne]
  exact ⟨(all _ (by decide)).trans (allInitializerGlobals_sha_state state.globals),
    (all _ (by decide)).trans (allInitializerGlobals_sha_accelerator state.globals),
    (all _ (by decide)).trans (allInitializerGlobals_ssz_chunk state.globals),
    (all _ (by decide)).trans (allInitializerGlobals_zero_hashes state.globals)⟩

#print axioms main_decoder_hash_workspace_globals
end InitECandidate.Runtime
