import InitECandidate.Runtime.WitnessResolveModeSource
import InitECandidate.Runtime.BoundWordStoreChainFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_resolve_tail_memory_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top flag pointer length hash watched : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "r") = some
      (.rStruct [.val (.word flag),.val (.word pointer),.val (.word length),.val (.word hash)]))
    (separate : watched ≠ top+80) :
    (evaluateHOLFiniteState s witnessResolveTail).2.memory watched=s.memory watched := by
  have storeFrame (expression : ExpHOL 64) (word : BitVec 64) (tail : ProgHOL 64)
      (readOnly : readOnlyMemory tail=true)
      (evaluated : ∀ state : PanSemStateFiniteExact 64 F, state.locals=s.locals →
        @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) expression=some (.val (.word word))) :
      (evaluateHOLFiniteState s (.seq (.store (.op .add [.var .local (ofString "top"),.const 80]) expression) tail)).2.memory watched=s.memory watched := by
    have supported : BoundWordStoreChainFrame (F := F) s.locals watched
        (.seq (.store (.op .add [.var .local (ofString "top"),.const 80]) expression) tail) := by
      apply BoundWordStoreChainFrame.store
      · intro state locals
        refine ⟨top+80,?_,separate⟩
        simp [evalHOLExact,evalListHOLExact,locals,atTop,wordOpHOL,wordOp,valueIsWord,valueWord]
      · intro state locals parsed actual
        exact ⟨word,Option.some.inj (actual.symm.trans (evaluated state locals))⟩
      exact .tail _ readOnly
    exact evaluate_boundWordStoreChain_frame supported s rfl
  have completed := storeFrame (.const 0) 0
    (.seq (.assign .local (ofString "result") (.rfield 1 (.var .local (ofString "r"))))
      (.assign .local (ofString "mode") (.const 0))) rfl (by intro state locals; rfl)
  have pending := storeFrame (.rfield 3 (.var .local (ofString "r"))) hash
    (.seq (.assign .local (ofString "cur_p") (.rfield 1 (.var .local (ofString "r"))))
      (.seq (.assign .local (ofString "cur_n") (.rfield 2 (.var .local (ofString "r"))))
        (.assign .local (ofString "mode") (.const 1)))) rfl (by
      intro state locals
      simp [evalHOLExact,locals,atResult])
  rw [source_witness_resolve_tail,evaluateHOLFiniteState_ite]
  split
  · split
    · exact pending
    · exact completed
  · rfl

#print axioms witness_resolve_tail_memory_frame
end InitECandidate.Runtime
