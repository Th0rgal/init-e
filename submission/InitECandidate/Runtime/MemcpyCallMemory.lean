import InitECandidate.Runtime.MemcpyBodyMemory
import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memcpy_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (destination source size watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word destination),.val (.word source),.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (small : size.toNat ≤ 33806089496)
    (budget : size.toNat / 32 + size.toNat / 8 + 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update
      (ofString "src",.val (.word source))).update (ofString "n",.val (.word size))
  have installed : state.code.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
    rw [code]; exact originalRuntimeCode_memcpy_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memcpy) destination source size (by decide) (by decide) (by decide) installed
  obtain ⟨value,output,bodyRun,globals,_⟩ := evaluate_discard_normal_body_memory state post (ofString "memcpy")
    arguments [.val (.word destination),.val (.word source),.val (.word size)] (sourceFunctionBody Guest.guestFn_memcpy)
    callee .one args lookup run
  let entry := callEntryStateHOLFinite state callee
  have dstLocal : entry.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide,show ofString "src" ≠ ofString "dst" by decide]
  have srcLocal : entry.locals.lookup (ofString "src") = some (.val (.word source)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "src" by decide]
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [globals]
  exact memcpy_body_returned_memory entry output destination source size watched dstLocal srcLocal sizeLocal
    wordSeparate byteSeparate small (by change size.toNat / 32 + size.toNat / 8 + 10 ≤ state.clock - 1; omega) value bodyRun

#print axioms memcpy_call_normal_memory
end InitECandidate.Runtime
