import InitECandidate.Runtime.HtrHeapGlobals
import InitECandidate.Runtime.HtrPbytesReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPbytes_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_pbytes") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrPbytes_lookup
    (NormalRel.returned htrPbytes_normal_heapGlobals)

theorem htrPbytes_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (p n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_pbytes") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrPbytes_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrPbytes_call_normal_heap state post arguments p n out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrPbytes_call_heapGlobals
#print axioms htrPbytes_call_normal_globals
end InitECandidate.Runtime
