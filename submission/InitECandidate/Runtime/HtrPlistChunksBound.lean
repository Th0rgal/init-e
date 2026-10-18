import InitECandidate.Runtime.ProgressiveCallBound
import InitECandidate.Runtime.MixInLengthBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPlistChunksCost : Nat := (progressiveBodyCost + 1) + 156

theorem runBounded_htrPlistChunks_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (roots n out heap : BitVec 64)
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrPlistChunksCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_plist_chunks) htrPlistChunksCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (.seq
    (.call (some (none,none)) (ofString "merkleize_progressive")
      [.var .local (ofString "roots"),.var .local (ofString "n"),.var .local (ofString "out")])
    (.seq (.call (some (none,none)) (ofString "mix_in_length")
      [.var .local (ofString "out"),.var .local (ofString "len"),.var .local (ofString "out")])
      (.return (.const 0)))) htrPlistChunksCost
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "roots"),.var .local (ofString "n"),.var .local (ofString "out")] =
      some [.val (.word roots),.val (.word n),.val (.word out)] := by
    simp [evalListHOLExact,evalHOLExact,hr,hn,ho]
  exact RunBounded.seq (runBounded_progressive_call state none _ roots n out heap args small hh heapBound code
    (by unfold htrPlistChunksCost at budget; omega)) budget (by
      intro next normal nextCode remaining
      apply RunBounded.ofProg _ (nextCode.trans code) remaining
      exact ProgBounded.seq (ProgBounded.call mixInLength_funBounded _ _) (ProgBounded.straight _ (by decide)))

#print axioms runBounded_htrPlistChunks_body
end InitECandidate.Runtime
