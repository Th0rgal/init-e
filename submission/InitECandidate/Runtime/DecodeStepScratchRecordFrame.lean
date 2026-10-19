import InitECandidate.Runtime.ScratchParserReturnedEnvironment
import InitECandidate.Runtime.DecodeStepBranchScratchProgress
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem fresh_scratch_record_separate (record scratch watched : BitVec 64)
    (fits : record.toNat+88 ≤ scratch.toNat) (above : scratch.toNat ≤ watched.toNat) :
    ∀ offset : Nat, offset < 88 → watched ≠ record+BitVec.ofNat 64 offset := by
  intro offset inside same
  have literal : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have addNat : (record+BitVec.ofNat 64 offset).toNat = record.toNat+offset := by
    rw [BitVec.toNat_add_of_lt (by rw [literal]; have := scratch.isLt; omega),literal]
  have equal := congrArg BitVec.toNat same
  rw [addNat] at equal
  omega

theorem source_decode_step_branch_stores_frame : decodeStepBranchStores =
  .seq (.store (.op .add [.var .local (ofString "rec2"),.const 8]) (.const 2))
  (.seq (.store (.op .add [.var .local (ofString "rec2"),.const 16]) (.var .local (ofString "br")))
  (.seq (.store (.op .add [.var .local (ofString "rec2"),.const 24]) (.var .local (ofString "arr")))
  (.seq (.store (.op .add [.var .local (ofString "rec2"),.const 32]) (.const 0))
  (.seq (.store (.op .add [.var .local (ofString "rec2"),.const 40]) (.const 0))
  (.seq (.store (.op .add [.var .local (ofString "rec2"),.const 48]) (.var .local (ofString "p")))
  (.seq (.store (.op .add [.var .local (ofString "rec2"),.const 56]) (.var .local (ofString "n")))
    (.return (.rstruct [.const 1,.var .local (ofString "rec2")])))))))) := by
  simp only [decodeStepBranchStores,decodeStepBranchRecord,decodeStepBranchConstruction,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem decode_step_extension_stores_upper_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (record scratch watched arr p n nibs count leaf : BitVec 64)
    (atRecord : s.locals.lookup (ofString "rec") = some (.val (.word record)))
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (atPath : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (fits : record.toNat+88 ≤ scratch.toNat) (above : scratch.toNat ≤ watched.toNat) :
    (evaluateHOLFiniteState s decodeStepExtensionStores).2.memory watched = s.memory watched := by
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched decodeStepExtensionStores := by
    rw [source_decodeStep_extension_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+8,?_,fresh_scratch_record_separate record scratch watched fits above 8 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨1,by simpa [evalHOLExact] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+24,?_,fresh_scratch_record_separate record scratch watched fits above 24 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨arr,by simpa [evalHOLExact,locals,at_arr] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+48,?_,fresh_scratch_record_separate record scratch watched fits above 48 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨p,by simpa [evalHOLExact,locals,at_p] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+56,?_,fresh_scratch_record_separate record scratch watched fits above 56 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨n,by simpa [evalHOLExact,locals,at_n] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+64,?_,fresh_scratch_record_separate record scratch watched fits above 64 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨nibs,by simpa [evalHOLExact,locals,atPath] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+72,?_,fresh_scratch_record_separate record scratch watched fits above 72 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨count,by simpa [evalHOLExact,locals,atPath] using evaluated.symm⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

/-- Actual returned extension record writes stay below the old scratch frontier. -/
theorem decode_step_extension_record_returned_upper_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame arr p n nibs count leaf : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (atPath : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepExtensionRecord = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = s.globals.lookup (ofString "heap_ptr") ∧
      ∀ watched : BitVec 64, scratch.toNat ≤ watched.toNat → post.memory watched = s.memory watched := by
  rw [source_decodeStep_extension_record] at run
  obtain ⟨ready,output,locals,memory,heap,readyCode,tailRun,postMemory,postGlobals,recordBefore⟩ :=
    scratch_parser_declaration_returned_environment s post scratch frame (ofString "rec") decodeStepExtensionStores value
      scratchGlobal frameGlobal ordered code ticks run
  have atRecord : ready.locals.lookup (ofString "rec") = some (.val (.word (scratchAllocationEnd scratch 88))) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "rec" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globalFrame : OriginalGlobalsFrame decodeStepExtensionStores := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_decodeStep_extension_stores]
    rfl
  have globals := globalFrame ready (readyCode.trans code)
  rw [tailRun] at globals
  refine ⟨?_,?_⟩
  · rw [postGlobals,globals]
    exact heap
  · intro watched above
    have frameMemory := decode_step_extension_stores_upper_frame ready (scratchAllocationEnd scratch 88) scratch watched arr p n nibs count leaf atRecord
      ((other _ (by decide)).trans at_arr)
      ((other _ (by decide)).trans at_p)
      ((other _ (by decide)).trans at_n)
      ((other _ (by decide)).trans atPath)
      recordBefore above
    rw [tailRun] at frameMemory
    exact (congrFun postMemory watched).trans (frameMemory.trans (congrFun memory watched))

#print axioms decode_step_extension_stores_upper_frame
#print axioms decode_step_extension_record_returned_upper_frame

theorem decode_step_branch_stores_upper_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (record scratch watched br arr p n : BitVec 64)
    (atRecord : s.locals.lookup (ofString "rec2") = some (.val (.word record)))
    (at_br : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (fits : record.toNat+88 ≤ scratch.toNat) (above : scratch.toNat ≤ watched.toNat) :
    (evaluateHOLFiniteState s decodeStepBranchStores).2.memory watched = s.memory watched := by
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched decodeStepBranchStores := by
    rw [source_decode_step_branch_stores_frame]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+8,?_,fresh_scratch_record_separate record scratch watched fits above 8 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨2,by simpa [evalHOLExact] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+16,?_,fresh_scratch_record_separate record scratch watched fits above 16 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨br,by simpa [evalHOLExact,locals,at_br] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+24,?_,fresh_scratch_record_separate record scratch watched fits above 24 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨arr,by simpa [evalHOLExact,locals,at_arr] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+32,?_,fresh_scratch_record_separate record scratch watched fits above 32 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨0,by simpa [evalHOLExact] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+40,?_,fresh_scratch_record_separate record scratch watched fits above 40 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨0,by simpa [evalHOLExact] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+48,?_,fresh_scratch_record_separate record scratch watched fits above 48 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨p,by simpa [evalHOLExact,locals,at_p] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨record+56,?_,fresh_scratch_record_separate record scratch watched fits above 56 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨n,by simpa [evalHOLExact,locals,at_n] using evaluated.symm⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

/-- Actual returned branch record writes stay below the old scratch frontier. -/
theorem decode_step_branch_record_returned_upper_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame br arr p n : BitVec 64)
    (at_br : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepBranchRecord = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = s.globals.lookup (ofString "heap_ptr") ∧
      ∀ watched : BitVec 64, scratch.toNat ≤ watched.toNat → post.memory watched = s.memory watched := by
  rw [source_decode_step_branch_record] at run
  obtain ⟨ready,output,locals,memory,heap,readyCode,tailRun,postMemory,postGlobals,recordBefore⟩ :=
    scratch_parser_declaration_returned_environment s post scratch frame (ofString "rec2") decodeStepBranchStores value
      scratchGlobal frameGlobal ordered code ticks run
  have atRecord : ready.locals.lookup (ofString "rec2") = some (.val (.word (scratchAllocationEnd scratch 88))) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "rec2" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globalFrame : OriginalGlobalsFrame decodeStepBranchStores := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_decode_step_branch_stores_frame]
    rfl
  have globals := globalFrame ready (readyCode.trans code)
  rw [tailRun] at globals
  refine ⟨?_,?_⟩
  · rw [postGlobals,globals]
    exact heap
  · intro watched above
    have frameMemory := decode_step_branch_stores_upper_frame ready (scratchAllocationEnd scratch 88) scratch watched br arr p n atRecord
      ((other _ (by decide)).trans at_br)
      ((other _ (by decide)).trans at_arr)
      ((other _ (by decide)).trans at_p)
      ((other _ (by decide)).trans at_n)
      recordBefore above
    rw [tailRun] at frameMemory
    exact (congrFun postMemory watched).trans (frameMemory.trans (congrFun memory watched))

#print axioms decode_step_branch_stores_upper_frame
#print axioms decode_step_branch_record_returned_upper_frame
end InitECandidate.Runtime
