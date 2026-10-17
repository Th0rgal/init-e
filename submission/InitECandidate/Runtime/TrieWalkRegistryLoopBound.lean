import InitECandidate.Runtime.TrieWalkRegistryStepContract
import InitECandidate.Runtime.RankedLoopReturnsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original traversal loop has a finite clock bound once the constructor
registries and nibble buffer invariant have been established. -/
theorem evaluate_trieWalk_registry_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (small : length.toNat ≤ 64) (member : node = 0 ∨ node ∈ live)
    (registry : TrieWalkRegistry live extensions branches state)
    (nibbles : TrieNibbleRange state nibs length)
    (ticks : trieWalkLoopRank length state * 258 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state trieWalkLoop = (result,post) ∧
      state.clock ≤ post.clock + trieWalkLoopRank length state * 258 ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post.locals.lookup (ofString "node") = some (.val (.word (0 : BitVec 64))) ∧
        TrieWalkRegistry live extensions branches post ∧ TrieNibbleRange post nibs length) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    (∃ node index : BitVec 64,
      current.locals.lookup (ofString "node") = some (.val (.word node)) ∧
      current.locals.lookup (ofString "pos") = some (.val (.word index)) ∧
      index.toNat ≤ length.toNat ∧ (node = 0 ∨ node ∈ live)) ∧
    current.locals.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
    current.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
    current.code = originalRuntimeCode ∧ TrieWalkRegistry live extensions branches current ∧
    TrieNibbleRange current nibs length
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "node")) (.const 0)) =
      some (.val (.word (if trieWalkLoopRank length current = 0 then 0 else 1))) := by
    rintro current ⟨⟨node,index,atNode,atPos,bound,liveNode⟩,rest⟩
    exact eval_trieWalk_loop_rank_guard current node length atNode
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨bindings,atNibs,atLength,code,registered,range⟩
    exact ⟨bindings,atNibs,atLength,code,registered.after_memory rfl,range.after_frame rfl rfl rfl⟩
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F,
      trieWalkLoopRank length (decClockHOLFinite current) = trieWalkLoopRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < trieWalkLoopRank length current → 257 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 257 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current trieWalkStep = (none,post) ∧ invariant post ∧
          trieWalkLoopRank length post < trieWalkLoopRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
          evaluateHOLFiniteState current trieWalkStep = (some result,post))) := by
    rintro current ⟨⟨node,index,atNode,atPos,bound,liveNode⟩,atNibs,atLength,code,registered,range⟩ positive ticks
    have nonzero : node ≠ 0 := by
      intro zero
      simp [trieWalkLoopRank,atNode,zero] at positive
    have liveMember : node ∈ live := liveNode.resolve_left nonzero
    obtain ⟨result,post,run,cost,remaining,noTimeout,noBreak,noContinue,normal⟩ :=
      evaluate_trieWalk_registry_step_contract current live extensions branches node nibs index length
        atNode atNibs atPos atLength code bound small nonzero liveMember registered range ticks
    refine ⟨post,cost,remaining,?_⟩
    cases result with
    | none =>
      obtain ⟨child,next,childLocal,nextLocal,nibsLocal,lengthLocal,nextBound,liveChild,code,registry,range,decrease⟩ := normal rfl
      exact Or.inl ⟨run,⟨⟨child,next,childLocal,nextLocal,nextBound,liveChild⟩,nibsLocal,lengthLocal,code,registry,range⟩,decrease⟩
    | some result => exact Or.inr ⟨result,by simpa using noContinue,by simpa using noTimeout,by simpa using noBreak,run⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,done⟩ := evaluate_ranked_loop_returns_invariant
    (.cmp .notEqual (.var .local (ofString "node")) (.const 0)) trieWalkStep invariant
    (trieWalkLoopRank length) 257 guard enter sameRank step state
    ⟨⟨node,index,nodeLocal,posLocal,bounded,member⟩,nibsLocal,nlenLocal,code,registry,nibbles⟩ ticks
  refine ⟨result,post,?_,cost,remaining,noTimeout,?_⟩
  · rw [source_trieWalk_loop]; exact run
  · intro normal
    obtain ⟨⟨⟨node,index,atNode,atPos,bound,member⟩,atNibs,atLength,code,registry,range⟩,rankZero⟩ := done normal
    have zero : node = 0 := by
      by_contra nonzero
      simp [trieWalkLoopRank,atNode] at rankZero
      exact nonzero rankZero
    exact ⟨by simpa [zero] using atNode,registry,range⟩

#print axioms evaluate_trieWalk_registry_loop_bounded
end InitECandidate.Runtime
