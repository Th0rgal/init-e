import InitECandidate.Runtime.ProgressiveStepBound
import InitECandidate.Runtime.MerkleizeReturnedHeap
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressive_after_clip_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p off cnt size roots k heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hc : state.locals.lookup (ofString "cnt") = some (.val (.word cnt)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state progressiveAfterClip = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    ∀ key, post.locals.lookup key = (progressiveUpdateState state off size k).locals.lookup key := by
  rw [source_progressive_after_clip,evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "merkleize") progressiveMerkleArguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some result => cases run
    | none =>
      have frame : ∀ key, middle.locals.lookup key = state.locals.lookup key := by
        intro key
        have kept := evaluate_avoidsLocal_flowing key
          (.call (some (none,none)) (ofString "merkleize") progressiveMerkleArguments) rfl state
          (by rw [callRun]; exact Or.inl rfl)
        rw [callRun] at kept
        exact kept
      have heapKept := merkleize_call_normal_heap state middle progressiveMerkleArguments
        (p + off * 32) cnt size (roots + k * 32) heap
        (progressive_arguments state p off cnt size roots k hp ho hc hs hr hk) code hh callRun
      have updates := evaluate_progressive_updates middle off size k
        ((frame _).trans ho) ((frame _).trans hs) ((frame _).trans hk)
      dsimp only at run
      rw [updates] at run
      cases run
      refine ⟨heapKept,?_⟩
      intro key
      simp only [progressiveUpdateState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      split <;> first | rfl | skip
      exact frame key

theorem progressive_step_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p n off size roots k heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state progressiveStep = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    ∀ key, key ≠ ofString "cnt" →
      post.locals.lookup key = (progressiveUpdateState state off size k).locals.lookup key := by
  rw [source_progressive_step] at run
  have init : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .sub [.var .local (ofString "n"),.var .local (ofString "off")]) =
      some (.val (.word (n - off))) := by
    simp [evalHOLExact,evalListHOLExact,hn,ho,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "cnt") _
    (n - off) _ none init run
  rw [evaluateHOLFiniteState_seq_line780,evaluate_progressive_clip state n off size hs] at bodyRun
  dsimp only at bodyRun
  have fields := progressive_after_clip_normal (progressiveClippedState state n off size) inner
    p off (progressiveChunkCount n off size) size roots k heap
    (by rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hp)
    (by rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact ho)
    (progressive_clipped_count state n off size)
    (by rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hs)
    (by rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hr)
    (by rw [progressive_clipped_other_local _ _ _ _ _ (by decide)]; exact hk)
    (by unfold progressiveClippedState; split <;> exact hh)
    (by unfold progressiveClippedState; split <;> exact code) bodyRun
  constructor
  · rw [scope]; exact fields.1
  · intro key different
    rw [scope]
    change (HolFiniteMapExact.resVarEq inner.locals _).lookup key = _
    rw [resVarEq_lookup,if_neg different,fields.2]
    simp only [progressiveUpdateState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    split <;> first | rfl | skip
    split <;> first | rfl | skip
    split <;> first | rfl | skip
    exact progressive_clipped_other_local state n off size key different

#print axioms progressive_step_normal
#print axioms progressive_after_clip_normal
end InitECandidate.Runtime
