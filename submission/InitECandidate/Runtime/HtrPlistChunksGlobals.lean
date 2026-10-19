import InitECandidate.Runtime.HtrHeapGlobals
import InitECandidate.Runtime.HtrPlistChunksCallHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normally returned original list-of-chunks calls restore the complete
global map after progressive hashing and the length mix-in. -/
theorem htrPlistChunks_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer count length out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word count),.val (.word length),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_plist_chunks") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrPlistChunks_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrPlistChunks_call_normal_heap state post arguments pointer count length out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrPlistChunks_call_normal_globals
end InitECandidate.Runtime
