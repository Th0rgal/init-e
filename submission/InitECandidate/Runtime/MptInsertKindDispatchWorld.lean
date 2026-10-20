import InitECandidate.Runtime.MptInsertChoiceWorld
import InitECandidate.Runtime.MptInsertGuardNormal
import InitECandidate.Runtime.NodeInvalidateNibbleWorld
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The full real kind dispatch includes invalid-kind rejection and cache
invalidation before its continuing path. All key/frame facts cross those
actual calls, with strict traversal progress retained. -/
theorem mpt_insert_kind_dispatch_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level length kind oldResult oldNode oldSlot oldLevel : BitVec 64)
 (member : node∈live) (capacity : 32≤size node)
 (atKind : s.locals.lookup (ofString "k")=some (.val (.word kind)))
 (kindField : s.memory node=.word kind)
 (nibbles : TrieNibbleRange s key length)
 (keyAligned : key.toNat%8=0) (recordBefore : node.toNat+32≤key.toNat)
 (keyExtent : key.toNat+length.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertKindDispatch=(none,post)) :
 ∃child slot nextLevel : BitVec 64, AllocatedTrieWorld post live extensions branches size frontier ∧
 TrieNibbleRange post key length ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word slot)) ∧
 post.memory slot=.word child ∧TrieChildSlot post extensions branches slot ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word nextLevel)) ∧
 level.toNat<nextLevel.toNat ∧nextLevel.toNat≤length.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.globals=s.globals ∧
 (∀watched : BitVec 64,watched≠node+8 →watched≠node+16 →watched≠node+24 →post.memory watched=s.memory watched) := by
 rw [source_mptInsert_kind_dispatch] at run
 obtain ⟨guarded,guardRun,tailRun⟩:=seq_normal_parts run
 obtain ⟨nonzero,identity⟩:=mpt_insert_guard_normal_identity s guarded kind atKind code guardRun
 subst guarded
 obtain ⟨ready,invalidateRun,choiceRun⟩:=seq_normal_parts tailRun
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "node")]=some [.val (.word node)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNode]
 have actualInvalidate:=invalidateRun
 rw [source_mptInsert_invalidate] at actualInvalidate
 obtain ⟨readyWorld,readyNibbles,locals,globals,frame⟩:=node_invalidate_discard_nibble_world s ready live extensions branches size frontier node key length
  world member capacity nibbles keyAligned recordBefore keyExtent _ args fullDomain code actualInvalidate
 have different (offset : Nat) (positive : 0<offset) (small : offset<32) : node≠node+BitVec.ofNat 64 offset := by
  intro equal
  have natural:=congrArg BitVec.toNat equal
  rw [world.layout.field_nat node member offset (by omega)] at natural
  omega
 have readyKind : ready.memory node=.word kind := by
  rw [frame node (different 8 (by decide) (by decide)) (different 16 (by decide) (by decide)) (different 24 (by decide) (by decide))]
  exact kindField
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertInvalidate
 rw [invalidateRun] at metadata
 have bounded:=mpt_insert_invalidate_bounded s code (by omega)
 unfold RunBounded at bounded
 rw [invalidateRun] at bounded
 have readyCode : ready.code=originalRuntimeCode:=metadata.1.trans code
 obtain ⟨child,slot,nextLevel,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevelAt,advanced,fits,go,memory,globalOut⟩:=
  mpt_insert_kind_choice_world ready post live extensions branches size frontier readyWorld node key level length kind oldResult oldNode oldSlot oldLevel
   member (by rw [locals];exact atKind) readyKind nonzero readyNibbles keyExtent
   (by intro address small;rw [metadata.2.1];exact fullDomain address small)
   (by rw [locals];exact atNode) (by rw [locals];exact atKey) (by rw [locals];exact atLevel)
   (by rw [locals];exact atLength) (by rw [locals];exact atResult) (by rw [locals];exact atNextNode)
   (by rw [locals];exact atNextSlot) (by rw [locals];exact atNextLevel) (by rw [locals];exact zero)
   inside short readyCode (by have:=bounded.1;dsimp only at this;omega) running choiceRun
 refine ⟨child,slot,nextLevel,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevelAt,advanced,fits,go,globalOut.trans globals,?_⟩
 intro watched n8 n16 n24
 rw [memory]
 exact frame watched n8 n16 n24

#print axioms mpt_insert_kind_dispatch_world
end InitECandidate.Runtime
