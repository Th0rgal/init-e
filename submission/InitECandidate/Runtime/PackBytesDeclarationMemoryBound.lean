import InitECandidate.Runtime.PackBytesReturned
import InitECandidate.Runtime.PackBytesMemoryFrame
import InitECandidate.Runtime.OriginalPackBytesCode
import InitECandidate.Runtime.PanTwoWordLookupShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_packBytes_declaration_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailCost : Nat)
    (p n heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (aligned : heap.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode)
    (budget : packBytesBodyCost + 1 + tailCost ≤ state.clock)
    (tail : ∀ post : PanSemStateFiniteExact 64 F,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (packBytesCount n * (32#64))))) →
      (allocationEnd heap (packBytesCount n * (32#64))).toNat ≤ 33806089496 →
      post.code = state.code →
      (∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = state.memory watched) →
      tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name (.rStruct [.val (.word heap),.val (.word (packBytesCount n))])
        {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name (.comb [.one,.one]) (ofString "pack_bytes") arguments continuation)
      (packBytesBodyCost + 1 + tailCost) := by
  refine RunBounded.decCall (bodyCost := packBytesBodyCost) args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "pack_bytes") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pack_bytes,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_packBytes_lookup
  rw [pan_two_word_lookup_shape state.code.lookup (ofString "pack_bytes") (ofString "p") (ofString "n")
    (sourceFunctionBody Guest.guestFn_pack_bytes) (.comb [.one,.one]) p n (by decide) installed] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word p))).update (ofString "n",.val (.word n)))
  have hp : entry.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have hn : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  constructor
  · exact runBounded_packBytes_body entry p n heap hp hn hh small heapBound code
      (by change packBytesBodyCost ≤ state.clock - 1; omega)
  · intro value post run remaining
    have returned := packBytes_body_returned entry post n heap value hn hh heapBound code
      (by change 2 ≤ state.clock - 1; unfold packBytesBodyCost at budget; omega) run
    have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_pack_bytes)
    rw [run] at meta'
    rw [returned.1]
    have memory (watched : BitVec 64) (before : watched.toNat < heap.toNat) :
        post.memory watched = state.memory watched :=
      packBytes_body_returned_memory_frame entry post p n heap watched value hp hn hh heapBound code small aligned before
        (by change merkleMemoryCallCost + 2 ≤ state.clock - 1; unfold packBytesBodyCost at budget; omega) run
    exact tail post returned.2.1 returned.2.2 meta'.1 memory remaining

#print axioms runBounded_packBytes_declaration_memory
end InitECandidate.Runtime
