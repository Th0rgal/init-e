import InitECandidate.Runtime.ProgressivePureSteps
import InitECandidate.Runtime.MerkleizeCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressive_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p off cnt size roots k : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hc : state.locals.lookup (ofString "cnt") = some (.val (.word cnt)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) progressiveMerkleArguments =
      some [.val (.word (p + off * 32)),.val (.word cnt),.val (.word size),.val (.word (roots + k * 32))] := by
  simp [progressiveMerkleArguments,evalListHOLExact,evalHOLExact,hp,ho,hc,hs,hr,hk,
    wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

theorem runBounded_progressive_after_clip {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p off cnt size roots k heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hc : state.locals.lookup (ofString "cnt") = some (.val (.word cnt)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (small : cnt.toNat ≤ 134217712)
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleBodyCost + 1 ≤ state.clock) :
    RunBounded state progressiveAfterClip (merkleBodyCost + 1) := by
  rw [source_progressive_after_clip]
  have first := runBounded_merkleize_call state none progressiveMerkleArguments
    (p + off * 32) cnt size (roots + k * 32) heap
    (progressive_arguments state p off cnt size roots k hp ho hc hs hr hk) small hh heapBound code budget
  have combined := RunBounded.seq (b := 0) first (by simpa using budget) (by
    intro next normal nextCode remaining
    exact RunBounded.ofProg progressive_pure_bounds.2 (nextCode.trans code) remaining)
  simpa using combined

theorem runBounded_progressive_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n off size roots k heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (small : n.toNat ≤ 134217712) (within : off.toNat ≤ n.toNat)
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleBodyCost + 1 ≤ state.clock) :
    RunBounded state progressiveStep (merkleBodyCost + 1) := by
  rw [source_progressive_step]
  apply RunBounded.decWord state (ofString "cnt") _ (n - off)
  · simp [evalHOLExact,evalListHOLExact,hn,ho,wordOpHOL,wordOp,valueIsWord,valueWord]
  · have clip := evaluate_progressive_clip state n off size hs
    have combined := RunBounded.seq
      (state := setVarHOLFinite (ofString "cnt") (.val (.word (n - off))) state)
      (first := progressiveClip) (tail := progressiveAfterClip) (a := 0) (b := merkleBodyCost + 1)
      (RunBounded.ofProg progressive_pure_bounds.1 (by exact code) (by omega))
      (by exact budget) (by
        intro next normal nextCode remaining
        rw [clip] at normal
        cases normal
        apply runBounded_progressive_after_clip _ p off (progressiveChunkCount n off size) size roots k heap
        · rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hp
        · rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact ho
        · exact progressive_clipped_count state n off size
        · rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hs
        · rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hr
        · rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hk
        · exact (progressive_chunk_bound n off size within).trans small
        · unfold progressiveClippedState
          split <;> exact hh
        · exact heapBound
        · exact nextCode.trans code
        · exact remaining)
    simpa using combined

#print axioms runBounded_progressive_step
#print axioms progressive_arguments
#print axioms runBounded_progressive_after_clip
end InitECandidate.Runtime
