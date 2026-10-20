import InitECandidate.Runtime.MptInsertStepWorld
import InitECandidate.Runtime.MptInsertStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Concrete active indexed-insertion invariant. Its rank reserves one final
iteration after the remaining key nibbles. No future execution is assumed. -/
structure MptInsertActive {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (rank : Nat) : Prop where
 world : AllocatedTrieWorld s live extensions branches size frontier
 nibbles : TrieNibbleRange s key length
 domain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address
 atKey : s.locals.lookup (ofString "key")=some (.val (.word key))
 atLength : s.locals.lookup (ofString "klen")=some (.val (.word length))
 atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer))
 atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength))
 path : ∃node slot level root : BitVec 64,
  s.locals.lookup (ofString "node")=some (.val (.word node)) ∧
  s.locals.lookup (ofString "slot")=some (.val (.word slot)) ∧
  s.locals.lookup (ofString "level")=some (.val (.word level)) ∧
  s.locals.lookup (ofString "result")=some (.val (.word root)) ∧
  (node=0 ∨node∈live) ∧(root=0 ∨root∈live) ∧
  (slot≠0 →TrieChildSlot s extensions branches slot) ∧
  (slot≠0 →s.memory slot=.word node) ∧
  level.toNat≤length.toNat ∧rank=length.toNat-level.toNat+1

theorem MptInsertActive.decClock {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 {frontier key length valuePointer valueLength : BitVec 64} {rank : Nat}
 (active : MptInsertActive s live extensions branches size frontier key length valuePointer valueLength rank) :
 MptInsertActive (decClockHOLFinite s) live extensions branches size frontier key length valuePointer valueLength rank := by
 exact ⟨active.world.after_memory_globals rfl rfl,active.nibbles.after_frame rfl rfl rfl,
  active.domain,active.atKey,active.atLength,active.atValue,active.atValueLength,active.path⟩

theorem MptInsertActive.inputs {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 {frontier key length valuePointer valueLength : BitVec 64} {rank : Nat}
 (active : MptInsertActive s live extensions branches size frontier key length valuePointer valueLength rank)
 (short : length.toNat≤18) : MptInsertInputs s := by
 obtain ⟨node,slot,level,root,a,b,c,d,e,f,g,h,inside,_⟩:=active.path
 exact ⟨node,key,length,level,valuePointer,valueLength,a,active.atKey,active.atLength,c,active.atValue,active.atValueLength,inside,short⟩

/-- The real whole insertion iteration preserves the concrete active world
and strictly lowers its natural rank whenever its real go flag remains live. -/
theorem mpt_insert_active_step {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (rank : Nat)
 (active : MptInsertActive s live extensions branches size frontier key length valuePointer valueLength rank)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 ∃nextRank,nextRank<rank ∧MptInsertActive post live extensions branches size frontier key length valuePointer valueLength nextRank := by
 obtain ⟨node,slot,level,root,a,b,c,d,validNode,validRoot,typed,backlink,inside,rankEq⟩:=active.path
 obtain ⟨child,nextSlot,nextLevel,nextRoot,world,nibbles,atNode,validChild,atSlot,newBacklink,newTyped,atLevel,advanced,fits,atRoot,validNextRoot,go,globals,locals⟩:=
  mpt_insert_step_world s post live extensions branches size frontier active.world node key level length slot root
   validNode validRoot (capacity node) active.nibbles aligned (recordsBefore node) keyExtent active.domain
   a active.atKey c active.atLength b d typed backlink inside short code budget running run
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertLoopStep
 rw [run] at metadata
 refine ⟨length.toNat-nextLevel.toNat+1,by omega,world,nibbles,?_,?_,?_,?_,?_,?_⟩
 · intro address small;rw [metadata.2.1];exact active.domain address small
 · exact (locals _ (by simp)).trans active.atKey
 · exact (locals _ (by simp)).trans active.atLength
 · exact (locals _ (by simp)).trans active.atValue
 · exact (locals _ (by simp)).trans active.atValueLength
 · exact ⟨child,nextSlot,nextLevel,nextRoot,atNode,atSlot,atLevel,atRoot,validChild,validNextRoot,
    fun _=>newTyped,fun _=>newBacklink,fits,rfl⟩

#print axioms MptInsertActive.inputs
#print axioms mpt_insert_active_step
end InitECandidate.Runtime
