import InitECandidate.Runtime.HeaderWithdrawalLoopFrame
import InitECandidate.Runtime.RlpWithdrawalHeap
import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.StoreControlFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem store_globals_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.store destination value)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_store]
  split <;> (try split) <;> (try split) <;> rfl

/-- One iteration's two slice stores and counter increment keep every cell outside the two slice
cells, and store exactly the two words of the *returned* encoder tuple. -/
theorem wd_slice_stores_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (slices counter buf total watched : BitVec 64)
    (atCounter : t.locals.lookup (ofString "i") = some (.val (.word counter)))
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word slices)))
    (atRecord : t.locals.lookup (ofString "e")
      = some (.rStruct [.val (.word buf),.val (.word total)]))
    (apart0 : watched ≠ slices + counter * 16#64)
    (apart8 : watched ≠ slices + counter * 16#64 + 8#64) :
    (evaluateHOLFiniteState t wdSliceLoopStores).2.memory watched = t.memory watched := by
  rw [wdSliceLoopStores]
  have addr0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .global (ofString "wd_rlp_slices"),
        .panop .mul [.var .local (ofString "i"), .const (16#64)]]) =
      some (.val (.word (slices + counter * 16#64))) := by
    simp [evalHOLExact,evalListHOLExact,panOpHOL,wordOpHOL,wordOp,valueIsWord,valueWord,atCounter,atSlices]
  have value0 : ∀ parsed, @evalHOLExact 64 F _ t.toExact
      (fun a => Classical.propDecidable (t.memaddrs a)) (.rfield 0 (.var .local (ofString "e")))
        = some parsed → ∃ word : BitVec 64, parsed = .val (.word word) := by
    intro parsed evaluated
    have actual : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.rfield 0 (.var .local (ofString "e"))) = some (.val (.word buf)) := by
      simp [evalHOLExact,atRecord]
    rw [actual] at evaluated
    exact ⟨buf,(Option.some.inj evaluated).symm⟩
  have value8 : ∀ parsed, @evalHOLExact 64 F _ t.toExact
      (fun a => Classical.propDecidable (t.memaddrs a)) (.rfield 1 (.var .local (ofString "e")))
        = some parsed → ∃ word : BitVec 64, parsed = .val (.word word) := by
    intro parsed evaluated
    have actual : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.rfield 1 (.var .local (ofString "e"))) = some (.val (.word total)) := by
      simp [evalHOLExact,atRecord]
    rw [actual] at evaluated
    exact ⟨total,(Option.some.inj evaluated).symm⟩
  have frame0 := evaluate_wordStore_memory_frame t
    (.op .add [.var .global (ofString "wd_rlp_slices"),
      .panop .mul [.var .local (ofString "i"), .const (16#64)]])
    (.rfield 0 (.var .local (ofString "e"))) (slices + counter * 16#64) watched addr0 value0 apart0
  have ctrl0 := evaluate_store_control_frame t
    (.op .add [.var .global (ofString "wd_rlp_slices"),
      .panop .mul [.var .local (ofString "i"), .const (16#64)]])
    (.rfield 0 (.var .local (ofString "e")))
  rw [evaluateHOLFiniteState_seq_line780]
  cases step0 : evaluateHOLFiniteState t (.store (.op .add [.var .global (ofString "wd_rlp_slices"),
      .panop .mul [.var .local (ofString "i"), .const (16#64)]])
      (.rfield 0 (.var .local (ofString "e")))) with
  | mk result0 middle0 =>
    rw [step0] at frame0 ctrl0
    dsimp only at frame0 ctrl0
    rcases ctrl0.1 with normal0 | failed0
    · subst normal0
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
      have globals0 : middle0.globals = t.globals := by
        have carried := store_globals_frame t
          (.op .add [.var .global (ofString "wd_rlp_slices"),
            .panop .mul [.var .local (ofString "i"), .const (16#64)]])
          (.rfield 0 (.var .local (ofString "e")))
        rw [step0] at carried
        exact carried
      have addr8 : @evalHOLExact 64 F _ middle0.toExact
          (fun a => Classical.propDecidable (middle0.memaddrs a))
          (.op .add [.var .global (ofString "wd_rlp_slices"),
            .panop .mul [.var .local (ofString "i"), .const (16#64)], .const (8#64)]) =
          some (.val (.word (slices + (counter * 16#64 + 8#64)))) := by
        simp [evalHOLExact,evalListHOLExact,panOpHOL,wordOpHOL,wordOp,valueIsWord,valueWord,ctrl0.2.1,
          globals0,atCounter,atSlices]
      have value8' : ∀ parsed, @evalHOLExact 64 F _ middle0.toExact
          (fun a => Classical.propDecidable (middle0.memaddrs a))
          (.rfield 1 (.var .local (ofString "e"))) = some parsed →
          ∃ word : BitVec 64, parsed = .val (.word word) := by
        intro parsed evaluated
        have actual : @evalHOLExact 64 F _ middle0.toExact
            (fun a => Classical.propDecidable (middle0.memaddrs a))
            (.rfield 1 (.var .local (ofString "e"))) = some (.val (.word total)) := by
          simp [evalHOLExact,ctrl0.2.1,atRecord]
        rw [actual] at evaluated
        exact ⟨total,(Option.some.inj evaluated).symm⟩
      have apart8' : watched ≠ slices + (counter * 16#64 + 8#64) := by
        rw [← BitVec.add_assoc]
        exact apart8
      have frame8 := evaluate_wordStore_memory_frame middle0
        (.op .add [.var .global (ofString "wd_rlp_slices"),
        .panop .mul [.var .local (ofString "i"), .const (16#64)], .const (8#64)])
        (.rfield 1 (.var .local (ofString "e"))) (slices + (counter * 16#64 + 8#64)) watched addr8
        value8' apart8'
      have ctrl8 := evaluate_store_control_frame middle0
        (.op .add [.var .global (ofString "wd_rlp_slices"),
        .panop .mul [.var .local (ofString "i"), .const (16#64)], .const (8#64)])
        (.rfield 1 (.var .local (ofString "e")))
      cases step8 : evaluateHOLFiniteState middle0 (.store (.op .add
          [.var .global (ofString "wd_rlp_slices"),
            .panop .mul [.var .local (ofString "i"), .const (16#64)], .const (8#64)])
          (.rfield 1 (.var .local (ofString "e")))) with
      | mk result8 middle8 =>
        rw [step8] at frame8 ctrl8
        dsimp only at frame8 ctrl8
        rcases ctrl8.1 with normal8 | failed8
        · subst normal8
          dsimp only
          have readOnly : readOnlyMemory
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const (1#64)])) = true := by
            simp [readOnlyMemory]
          have assignFrame := evaluate_readOnly_memory _ readOnly middle8
          rw [assignFrame]
          exact frame8.trans frame0
        · subst failed8
          exact frame8.trans frame0
    · subst failed0
      exact frame0

#print axioms wd_slice_stores_window
end InitECandidate.Runtime
