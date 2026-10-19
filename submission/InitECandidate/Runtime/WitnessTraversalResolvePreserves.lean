import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessResolveAllocationStack
import InitECandidate.Runtime.WitnessResolveResultAboveStack
import InitECandidate.Runtime.WitnessResolveModeDatabaseFrame
import InitECandidate.Runtime.WitnessResolveScratchChain
import InitECandidate.Runtime.WitnessResolveModeProgress
import InitECandidate.Runtime.WitnessResolveModeStateMeasure
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Normal execution of the original resolver preserves the concrete traversal
invariant, using its actual selected slot and actual returned control state. -/
theorem WitnessTraversalState.resolve_preserves {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (resolve : mode=2)
    (budget : resolveStepBodyCost layout.inputLimit+1≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) :
    WitnessTraversalInvariant layout post := by
  obtain ⟨array,slot,pointer,length,cell,readable,atSlot,slotBound,entry,lengthBound⟩ :=
    valid.resolve_arguments layout s scratch heap top mode go resolve
  have limit := valid.inputLimitBound
  have scratchLo := valid.scratchLower
  have scratchHi := valid.scratchBound
  have db := valid.scratchBeforeDatabase
  have floor := valid.databaseBeforeFloor
  have heapLo := valid.floorBeforeHeap
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  have tableAbove : scratch.toNat≤layout.table.toNat := by have h:=valid.tableAboveDatabase;omega
  have arrayAbove : scratch.toNat≤layout.dbArray.toNat := by have h:=valid.arrayAboveDatabase;omega
  have spanSize := entry.length_bound s array slot pointer length layout.input layout.inputLength
  have ticks : resolveStepBodyCost length.toNat+1≤s.clock := by
    have h:=resolveStepBodyCost_mono length.toNat layout.inputLimit lengthBound;omega
  obtain ⟨nonempty,selected⟩ := valid.resolveSelector resolve
  obtain ⟨topAbove,topPositive,topBefore⟩ := valid.scratchChain.head_bounds s top layout.scratchUpper scratch.toNat nonempty
  obtain ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,stackPost⟩ := witness_resolve_mode_normal_allocation_stack
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.heapAligned valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks layout.persistentFloor valid.floorBeforeHeap valid.stack run
  have aboveResult := witness_resolve_mode_result_above_stack
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.heapAligned valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks layout.persistentFloor valid.floorBeforeHeap valid.stack run
  have envelope := witness_resolve_mode_completed_node_envelope
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks run
  have progress := witness_resolve_mode_normal_progress
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top scratch.toNat layout.inputLimit
    valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks run
  obtain ⟨_,_,builtPost,entriesPost,slicesPost,domain,_,codePost,_⟩ := witness_resolve_mode_normal_database_frame
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.heapAligned valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks layout.databaseCeiling (by omega) topAbove (by omega) (by omega) valid.tableAboveDatabase valid.arrayAboveDatabase
    (by have h:=valid.dbHeapBeforeFloor;omega) run
  obtain ⟨_,_,topPost,chainPost,_⟩ := witness_resolve_mode_normal_scratch_chain
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.heapAligned valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks layout.scratchUpper (by omega) valid.scratchChain nonempty run
  have dbKept := evaluate_avoidsLocal_flowing (ofString "db") decodeWitnessNodeResolveMode
    (by rw [source_witness_resolve_mode,source_witness_resolve_call,source_witness_resolve_tail];decide) s
    (by rw [run];exact Or.inl rfl)
  rw [run] at dbKept
  have goKept := witness_resolve_go_normal_kept s post run
  have nodeEq (a b : BitVec 64)
      (h : some (ValueHOL.val (HolWordLab.word a))=some (.val (.word b))) : a=b :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj h))
  have nodeBounds (node : BitVec 64) (env : CompletedNodeEnvelope post node heap.toNat) :
      node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat) := by
    rcases env with zero | ⟨other,otherHeap,lo,hi,cap⟩
    · exact Or.inl zero
    · have same := nodeEq other nextHeap (otherHeap.symm.trans heapPost)
      subst other
      exact Or.inr ⟨by omega,hi⟩
  have completed : ∀ (atMode : post.locals.lookup (ofString "mode")=some (.val (.word (0#64)))),
      ∃ node : BitVec 64, post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat)) ∧
        WitnessResultAboveStack post layout.input layout.inputLength top node layout.persistentFloor scratch.toNat := by
    intro atMode
    rcases aboveResult with pending | ⟨node,_,atNode,resultAbove⟩
    · have bad := nodeEq (0#64) (1#64) (atMode.symm.trans pending);cases bad
    · rcases envelope with pending | ⟨other,_,atOther,env⟩
      · have bad := nodeEq (0#64) (1#64) (atMode.symm.trans pending);cases bad
      · have same := nodeEq other node (atOther.symm.trans atNode)
        subst other
        exact ⟨node,atNode,nodeBounds node env,resultAbove⟩
  have commonState (nextMode : BitVec 64)
      (atMode : post.locals.lookup (ofString "mode")=some (.val (.word nextMode)))
      (modes : nextMode=0 ∨ nextMode=1 ∨ nextMode=2)
      (decodeInput : nextMode=1 → ∃ p n : BitVec 64,
        post.locals.lookup (ofString "cur_p")=some (.val (.word p)) ∧
        post.locals.lookup (ofString "cur_n")=some (.val (.word n)) ∧
        layout.input.toNat≤p.toNat ∧ p.toNat+n.toNat≤layout.input.toNat+layout.inputLength.toNat ∧
        p.toNat+n.toNat<2^64 ∧ n.toNat≤layout.inputLength.toNat)
      (noResolve : nextMode≠2)
      (delivered : nextMode=0 → ∃ node : BitVec 64,
        post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat)) ∧
        WitnessResultAboveStack post layout.input layout.inputLength top node layout.persistentFloor scratch.toNat) :
      WitnessTraversalState layout post scratch nextHeap top nextMode go := by
    exact {
      code := codePost.trans valid.code
      atDb := dbKept.trans valid.atDb
      atTop := topPost
      atMode := atMode
      atGo := goKept.trans valid.atGo
      atScratch := scratchPost
      atFrame := framePost
      atHeap := heapPost
      floorBeforeHeap := valid.floorBeforeHeap.trans growth
      heapBound := capped
      heapAligned := aligned
      scratchArena := by intro a lo hi;rw [domain];exact valid.scratchArena a lo hi
      heapArena := by intro a lo hi;rw [domain];exact valid.heapArena a lo hi
      built := builtPost
      entries := entriesPost
      slices := slicesPost
      stack := stackPost
      scratchChain := chainPost
      modes := modes
      decodeInput := decodeInput
      resolveSelector := by intro bad;exact False.elim (noResolve bad)
      delivered := delivered
      framePositive := valid.framePositive
      scratchLower := valid.scratchLower
      scratchBound := valid.scratchBound
      scratchBeforeDatabase := valid.scratchBeforeDatabase
      databaseBeforeFloor := valid.databaseBeforeFloor
      inputRange := valid.inputRange
      inputBound := valid.inputBound
      inputLimitBound := valid.inputLimitBound
      inputBeforeFrame := valid.inputBeforeFrame
      tableAboveDatabase := valid.tableAboveDatabase
      arrayAboveDatabase := valid.arrayAboveDatabase
      dbHeapBeforeFloor := valid.dbHeapBeforeFloor
      dbArrayEnd := valid.dbArrayEnd
      goBits := valid.goBits
    }
  rcases progress.2.2 with ⟨modePost,_⟩ | ⟨p,n,modePost,atP,atN,lo,hi,nowrap,small⟩
  · exact ⟨scratch,nextHeap,top,0,go,commonState 0 modePost (Or.inl rfl)
      (by intro bad;cases bad) (by decide) (fun _ => completed modePost)⟩
  · exact ⟨scratch,nextHeap,top,1,go,commonState 1 modePost (Or.inr (Or.inl rfl))
      (fun _ => ⟨p,n,atP,atN,lo,hi,nowrap,small⟩) (by decide) (by intro bad;cases bad)⟩
#print axioms WitnessTraversalState.resolve_preserves
end InitECandidate.Runtime
