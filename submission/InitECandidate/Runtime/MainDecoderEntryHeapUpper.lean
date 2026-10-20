import InitECandidate.Runtime.MainBuffersHeapUpper
import InitECandidate.Runtime.CanonicalMainDecoderEntry
import InitECandidate.Runtime.MainBuffersReadyFields
import InitECandidate.Runtime.AllInitializerSszOffsets
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem MainDecoderEntry.fields_heap_upper {F : Type} {state ready : PanSemStateFiniteExact 64 F}
    (valid : MainDecoderEntry state ready) :
    ∃ length out zero heap : BitVec 64,
      ready.locals.lookup (ofString "inp") =
        some (.rStruct [.val (.word 2713731432),.val (.word length)]) ∧
      ready.locals.lookup (ofString "out") = some (.val (.word out)) ∧
      ready.locals.lookup (ofString "z32") = some (.val (.word zero)) ∧
      length.toNat ≤ 134217712 ∧ 2713731432 + length.toNat < 2 ^ 64 ∧
      ready.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344)) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0 ∧ 2713731432 ≤ heap.toNat ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.locals.lookup (ofString "si") = some (.val (.word 0)) ∧
      ready.locals.lookup (ofString "err_code") = some (.val (.word 0)) ∧
      heap.toNat≤2713731432+length.toNat+320 := by
  obtain ⟨buffers,_,bufferValid,_,locals,globals,code,domain⟩ := valid
  obtain ⟨length,out,zero,heap,inp,output,z32,small,fits,atHeap,capped,aligned,lower,installed,addresses,other,upper⟩ :=
    bufferValid.fields_heap_upper
  refine ⟨length,out,zero,heap,?_,?_,?_,small,fits,?_,?_,capped,aligned,lower,
    code.trans installed,domain.trans addresses,?_,?_,upper⟩
  · rw [locals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,ofString] using inp
  · rw [locals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,ofString] using output
  · rw [locals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,ofString] using z32
  · rw [globals,other _ (by decide)]
    exact allInitializerGlobals_ssz_offsets state.globals
  · rw [globals]
    exact atHeap
  · rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms MainDecoderEntry.fields_heap_upper
end InitECandidate.Runtime
