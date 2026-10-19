import InitECandidate.Runtime.WitnessBranchFinishProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual final child increment selects the complete final-value parser
and delivers the branch after restoring its saved parent link. -/
theorem witness_branch_last_child_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap prev : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word (15#64))))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (prevCell : s.memory top = .word prev) (topAbove : ceiling ≤ top.toNat)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s (witnessBranchAt 4) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
      post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
      post.memory top = s.memory top := by
  rw [source_witness_branch_increment] at run
  obtain ⟨selected,incrementRun,tailRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  obtain ⟨value,evaluated,selectedEq⟩ := evaluate_local_assign_normal_value s selected _ _ incrementRun
  have valueEq : value = .val (.word (16#64)) := by
    simpa [evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord] using evaluated.symm
  subst value
  have localFrame (name : MlS) (different : name ≠ ofString "i") :
      selected.locals.lookup name = s.locals.lookup name := by
    simp [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have selectedIndex : selected.locals.lookup (ofString "i") = some (.val (.word (16#64))) := by
    simp [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have condition : @evalHOLExact 64 F _ selected.toExact (fun a => Classical.propDecidable (selected.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.const 16)) = some (.val (.word (0#64))) := by
    simp [evalHOLExact,selectedIndex,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess]
  rw [source_witness_branch_dispatch,evaluateHOLFiniteState_ite,condition] at tailRun
  change evaluateHOLFiniteState selected (witnessBranchFinishAt 0) = (none,post) at tailRun
  have memory : selected.memory = s.memory := by rw [selectedEq]; rfl
  have domain : selected.memaddrs = s.memaddrs := by rw [selectedEq]; rfl
  have globals : selected.globals = s.globals := by rw [selectedEq]; rfl
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_branch_finish_normal_progress selected post
    array pointer length scratch frame top heap prev ceiling inputLimit
    (by rw [domain]; exact arrayReadable) (by rw [memory]; exact arrayCell)
    ((localFrame _ (by decide)).trans atTop) ((localFrame _ (by decide)).trans atBr)
    (by rw [memory]; exact prevCell) topAbove before heapBound (slice.after_frame s selected array 16 pointer length domain (congrFun memory _) (congrFun memory _))
    inputRange lengthBound limitBound (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (by rw [selectedEq]; exact code) orderedFrame framePositive scratchBelow
    (by intro address lower upper; rw [domain]; exact arena address lower upper)
    (by rw [selectedEq]; exact budget) tailRun
  exact ⟨topPost,resultPost,modePost.trans (localFrame _ (by decide)),cellPost.trans (congrFun memory top)⟩

#print axioms witness_branch_last_child_normal_progress
end InitECandidate.Runtime
