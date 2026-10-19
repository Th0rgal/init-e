import InitECandidate.Runtime.PackBytesDeclarationGlobalsBound
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.ReturnedCallClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Expose the real continuation of a returned packing declaration, including
its packed structure, allocation frontier, non-heap globals and prior memory. -/
theorem packBytes_declaration_returned_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (p n heap : BitVec 64) (value : ValueHOL 64) (tailCost : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (aligned : heap.toNat % 8 = 0) (code : state.code = originalRuntimeCode)
    (budget : packBytesBodyCost + 1 + tailCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "pack_bytes") arguments continuation) =
      (some (.returned value),post)) :
    ∃ ready output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState ready continuation = (some (.returned value),output) ∧
      post.memory = output.memory ∧
      ready.locals.lookup name = some (.rStruct [.val (.word heap),.val (.word (packBytesCount n))]) ∧
      (∀ key, key ≠ name → ready.locals.lookup key = state.locals.lookup key) ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (packBytesCount n * (32#64))))) ∧
      (allocationEnd heap (packBytesCount n * (32#64))).toNat ≤ 33806089496 ∧
      HeapRel state.globals ready.globals ∧ ready.code = state.code ∧
      (∀ watched : BitVec 64, watched.toNat < heap.toNat → ready.memory watched = state.memory watched) ∧
      tailCost ≤ ready.clock := by
  have installed : state.code.lookup (ofString "pack_bytes") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pack_bytes,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_packBytes_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "pack_bytes") (ofString "p") (ofString "n")
    (sourceFunctionBody Guest.guestFn_pack_bytes) (.comb [.one,.one]) p n (by decide) installed
  obtain ⟨returned,bodyPost,resumed,output,bodyRun,rlocals,rmem,rglobals,rclock,_,_,rcode,tail,scope⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope state post name (ofString "pack_bytes")
      (.comb [.one,.one]) (.comb [.one,.one]) arguments _ _ continuation _ value args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word p))).update (ofString "n",.val (.word n)))
  have hp : entry.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have hn : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : packBytesBodyCost ≤ entry.clock := by
    change packBytesBodyCost ≤ state.clock - 1
    exact Nat.le_sub_of_add_le ((Nat.le_add_right _ tailCost).trans budget)
  have result := packBytes_body_returned entry bodyPost n heap returned hn hh heapBound code
    (by change 2 ≤ state.clock - 1; unfold packBytesBodyCost at budget; omega) bodyRun
  have memory (watched : BitVec 64) (before : watched.toNat < heap.toNat) :=
    packBytes_body_returned_memory_frame entry bodyPost p n heap watched returned hp hn hh heapBound code small aligned before
      (by change merkleMemoryCallCost + 2 ≤ state.clock - 1; unfold packBytesBodyCost at budget; omega) bodyRun
  have globals := normalRel_apply packBytes_normal_heapRel
    (X := entry) (by rw [bodyRun]; exact Or.inr (Or.inr (Or.inr ⟨returned,rfl⟩))) (by exact code)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_pack_bytes)
  have spent := (runBounded_packBytes_body entry p n heap hp hn hh small heapBound code entryBudget).1
  rw [bodyRun] at globals metadata spent
  rw [result.1] at tail
  let ready := setVarHOLFinite name (.rStruct [.val (.word heap),.val (.word (packBytesCount n))]) resumed
  refine ⟨ready,output,tail,by rw [scope],?_,?_,?_,result.2.2,?_,?_,?_,?_⟩
  · simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key different
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,rlocals]
  · change resumed.globals.lookup _ = _
    rw [rglobals]; exact result.2.1
  · change HeapRel state.globals resumed.globals
    rw [rglobals]; exact globals
  · change resumed.code = state.code
    exact rcode.trans metadata.1
  · intro watched before
    change resumed.memory watched = state.memory watched
    rw [rmem]; exact memory watched before
  · change tailCost ≤ resumed.clock
    rw [rclock]
    exact returned_call_tail_clock state.clock bodyPost.clock packBytesBodyCost tailCost budget spent

#print axioms packBytes_declaration_returned_frame
end InitECandidate.Runtime
