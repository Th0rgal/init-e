import InitECandidate.Runtime.ScratchAllocationAligned
import InitECandidate.Runtime.WitnessTraversalStateTransport
import InitECandidate.Runtime.WitnessDecodeAllocationStack
import InitECandidate.Runtime.WitnessDecodeResultAboveStack
import InitECandidate.Runtime.WitnessDecodeModeDatabaseFrame
import InitECandidate.Runtime.WitnessDecodeScratchChain
import InitECandidate.Runtime.WitnessDecodeModeSelectedSlot
import InitECandidate.Runtime.WitnessDecodeCompletedNodeEnvelope
import InitECandidate.Runtime.WitnessModeCallerLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Actual normally completed decode mode preserves every component of the
concrete traversal invariant. No additional caller condition is assumed. -/
theorem WitnessTraversalState.decode_preserves {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (decode : mode=1)
    (budget : decodeStepBodyCost layout.inputLimit+1≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode=(none,post)) : WitnessTraversalInvariant layout post := by
  obtain ⟨pointer,length,atPointer,atLength,spanLo,spanHi,inputRange,size⟩ := valid.decodeInput decode
  have lengthBound := size.trans valid.inputBound
  have limit:=valid.inputLimitBound
  have scratchLo:=valid.scratchLower
  have scratchHi:=valid.scratchBound
  have db:=valid.scratchBeforeDatabase
  have floor:=valid.databaseBeforeFloor
  have heapLo:=valid.floorBeforeHeap
  have before:=valid.inputBeforeFloor
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have countLimit : layout.inputLimit*16<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  have heapArena : ∀ a : BitVec 64, heap.toNat≤a.toNat → a.toNat<33806089496 → s.memaddrs a := by
    intro a lo hi;exact valid.heapArena a (by omega) hi
  have beforeFrame : pointer.toNat+length.toNat≤layout.frame.toNat ∨ (scratch.toNat%8=0 ∧ scratch.toNat≤pointer.toNat) := by
    rcases valid.inputBeforeFrame with below | above
    · exact Or.inl (by omega)
    · exact Or.inr ⟨valid.scratchAligned,by omega⟩
  have beforeHeap : pointer.toNat+length.toNat≤heap.toNat := by omega
  have arrayAbove : scratch.toNat≤heap.toNat := by omega
  have floorAbove : scratch.toNat≤layout.persistentFloor := by omega
  have nodeEq (a b : BitVec 64)
      (h : some (ValueHOL.val (HolWordLab.word a))=some (.val (.word b))) : a=b :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj h))
  obtain ⟨builtPost,entriesPost,slicesPost,domain,_,codePost,_,nextHeap,heapPost,growth,capped,aligned⟩ :=
    witness_decode_mode_normal_database_frame s post layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit
    layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength valid.built valid.entries valid.slices
    (by have h:=valid.tableAboveDatabase;omega) (by have h:=valid.arrayAboveDatabase;omega)
    (by have h:=valid.dbHeapBeforeFloor;omega) (by have h:=valid.dbArrayEnd;have d:=valid.dbHeapBeforeFloor;omega) run
  obtain ⟨stackHeap,stackHeapPost,_,_,_,stackModes⟩ := witness_decode_mode_normal_allocation_stack s post layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit
    layout.input layout.inputLength layout.persistentFloor floorAbove heapLo spanLo spanHi valid.stack run
  have sameHeap := nodeEq stackHeap nextHeap (stackHeapPost.symm.trans heapPost)
  rw [sameHeap] at stackModes
  obtain ⟨framePost,chainModes⟩ := witness_decode_mode_normal_scratch_chain s post layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit
    layout.scratchUpper scratchHi (by omega) valid.scratchChain run
  have selectedModes := witness_decode_mode_normal_selected_slot s post layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit run
  have aboveResult := witness_decode_mode_result_above_stack s post layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit
    layout.input layout.inputLength layout.persistentFloor floorAbove heapLo spanLo spanHi valid.stack run
  have envelope := witness_decode_mode_completed_node_envelope s post layout.table pointer length scratch layout.frame heap scratch.toNat layout.inputLimit
    valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit run
  have dbPost := (witness_decode_mode_normal_db_kept s post run).trans valid.atDb
  have goPost := (witness_decode_go_normal_kept s post run).trans valid.atGo
  have nodeBounds (node : BitVec 64) (env : CompletedNodeEnvelope post node heap.toNat) :
      node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat) := by
    rcases env with zero | ⟨other,otherHeap,lo,hi,cap⟩
    · exact Or.inl zero
    · have same := nodeEq other nextHeap (otherHeap.symm.trans heapPost)
      rw [same] at hi
      exact Or.inr ⟨by omega,hi⟩
  have completed (modePost : post.locals.lookup (ofString "mode")=some (.val (.word (0#64)))) :
      ∃ node : BitVec 64, post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat)) ∧
        WitnessResultAboveStack post layout.input layout.inputLength top node layout.persistentFloor scratch.toNat := by
    rcases aboveResult with pending | ⟨node,_,atNode,resultAbove⟩
    · have bad := nodeEq (0#64) (2#64) (modePost.symm.trans pending);cases bad
    · rcases envelope with pending | ⟨other,_,atOther,env⟩
      · have bad := nodeEq (0#64) (2#64) (modePost.symm.trans pending);cases bad
      · have same := nodeEq other node (atOther.symm.trans atNode)
        rw [same] at env
        exact ⟨node,atNode,nodeBounds node env,resultAbove⟩
  have commonState (nextScratch nextTop nextMode : BitVec 64)
      (atScratch : post.globals.lookup (ofString "scratch_ptr")=some (.val (.word nextScratch)))
      (atTop : post.locals.lookup (ofString "top")=some (.val (.word nextTop)))
      (atMode : post.locals.lookup (ofString "mode")=some (.val (.word nextMode)))
      (scratchLower : layout.frame.toNat≤nextScratch.toNat) (scratchBound : nextScratch.toNat≤layout.scratchUpper)
      (scratchAligned : nextScratch.toNat%8=0)
      (stackPost : WitnessAllocationStack post layout.input layout.inputLength nextHeap layout.persistentFloor nextScratch.toNat nextTop)
      (chainPost : WitnessScratchChain post layout.scratchUpper nextScratch.toNat nextTop)
      (modes : nextMode=0 ∨ nextMode=1 ∨ nextMode=2)
      (decodeInput : nextMode=1 → ∃ p n : BitVec 64,
        post.locals.lookup (ofString "cur_p")=some (.val (.word p)) ∧ post.locals.lookup (ofString "cur_n")=some (.val (.word n)) ∧
        layout.input.toNat≤p.toNat ∧ p.toNat+n.toNat≤layout.input.toNat+layout.inputLength.toNat ∧ p.toNat+n.toNat<2^64 ∧ n.toNat≤layout.inputLength.toNat)
      (selector : nextMode=2 → nextTop≠0 ∧ WitnessSelectedSlot post nextTop)
      (delivered : nextMode=0 → ∃ node : BitVec 64, post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤nextHeap.toNat)) ∧
        WitnessResultAboveStack post layout.input layout.inputLength nextTop node layout.persistentFloor nextScratch.toNat) :
      WitnessTraversalState layout post nextScratch nextHeap nextTop nextMode go :=
    WitnessTraversalState.after_components layout s post scratch heap top mode go nextScratch nextHeap nextTop nextMode go
      valid domain codePost dbPost goPost atTop atMode atScratch framePost heapPost scratchLower scratchBound scratchAligned growth capped aligned
      builtPost entriesPost slicesPost stackPost chainPost valid.goBits modes decodeInput selector delivered
  rcases chainModes with ⟨modePost,topPost,scratchPost,chainPost⟩ | ⟨record,modePost,topPost,scratchPost,identity,recordLo,recordHi,chainPost⟩
  · rcases stackModes with ⟨_,_,stackPost⟩ | ⟨other,pending,_,_⟩
    · exact ⟨scratch,nextHeap,top,0,go,commonState scratch top 0 scratchPost topPost modePost scratchLo scratchHi valid.scratchAligned stackPost chainPost
        (Or.inl rfl) (by intro bad;cases bad) (by intro bad;cases bad) (fun _ => completed modePost)⟩
    · have bad := nodeEq (0#64) (2#64) (modePost.symm.trans pending);cases bad
  · rcases stackModes with ⟨pending,_,_⟩ | ⟨other,_,atOther,stackPost⟩
    · have bad := nodeEq (0#64) (2#64) (pending.symm.trans modePost);cases bad
    · have sameTop := nodeEq other record (atOther.symm.trans topPost)
      have stackRecord : WitnessAllocationStack post layout.input layout.inputLength nextHeap layout.persistentFloor record.toNat record := by
        simpa only [sameTop] using stackPost
      have selectedRecord : WitnessSelectedSlot post record := by
        rcases selectedModes with ⟨pending,_⟩ | ⟨other,atOther,_,_,_,_,_,_,_,selected⟩
        · have bad := nodeEq (0#64) (2#64) (pending.symm.trans modePost);cases bad
        · have same := nodeEq other record (atOther.symm.trans topPost)
          simpa only [same] using selected
      have positive : record≠0 := by
        intro zero
        have framePositive:=valid.framePositive
        rw [zero] at recordLo
        change layout.frame.toNat≤0 at recordLo
        omega
      exact ⟨record,nextHeap,record,2,go,commonState record record 2 scratchPost topPost modePost recordLo (by omega) (by rw [identity]; exact scratchAllocationEnd_aligned scratch 88)
        stackRecord chainPost (Or.inr (Or.inr rfl)) (by intro bad;cases bad) (fun _ => ⟨positive,selectedRecord⟩) (by intro bad;cases bad)⟩
#print axioms WitnessTraversalState.decode_preserves
end InitECandidate.Runtime
