import InitECandidate.Runtime.AllocationDeclarationNormalGeometry
import InitECandidate.Runtime.DecodeWitnessOuterTailBound
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.WordStoreNormalMemory
import InitECandidate.Runtime.AvoidsLocalFrame
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem decode_witness_attach_hash_normal_memory {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (node heap root : BitVec 64) (floor : Nat)
 (code : s.code=originalRuntimeCode)
 (atNode : s.locals.lookup (ofString "nd")=some (.val (.word node)))
 (atRoot : s.locals.lookup (ofString "root_hash")=some (.val (.word root)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapBound : heap.toNat≤33806089496) (aligned : heap.toNat%8=0) (aboveHeap : floor≤heap.toNat)
 (nodeBounds : node=0 ∨(floor≤node.toNat ∧node.toNat+32≤33806089496))
 (budget : 18≤s.clock) (run : evaluateHOLFiniteState s decodeWitnessAttachHash=(none,post)) :
 ∀watched : BitVec 64,watched.toNat<floor→post.memory watched=s.memory watched := by
 unfold decodeWitnessAttachHash at run
 rw [evaluateHOLFiniteState_ite] at run
 by_cases zero : node=0
 · subst node
   simp [evalHOLExact,atNode,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip] at run
   cases run
   intro watched hi;rfl
 · have nodeFloor : floor≤node.toNat ∧node.toNat+32≤33806089496 := nodeBounds.resolve_left zero
   simp only [evalHOLExact,atNode] at run
   simp [Compiler.Encoders.Asm.wordCmpHOL,show node≠0#64 from zero] at run
   obtain ⟨ready,output,tailRun,locals,memory,installed,_,clock,_,covers,within,postMemory⟩:=
    allocation_declaration_normal_geometry s post (ofString "h") (.const (32#64)) _ heap 32
     (by rw [evalListHOLFinite_eq_toExact];rfl) code atHeap heapBound run
   have fits : heap.toNat+32≤33806089496 := by change heap.toNat+32≤_ at covers;omega
   have atH : ready.locals.lookup (ofString "h")=some (.val (.word heap)) := by rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
   have nodeReady : ready.locals.lookup (ofString "nd")=some (.val (.word node)) := by rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atNode
   have rootReady : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)) := by rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRoot
   obtain ⟨copied,copyRun,storeRun⟩:=seq_normal_parts tailRun
   have copyArgs : evalListHOLFinite ready (h:=fun a=>Classical.propDecidable (ready.memaddrs a))
    [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const (32#64)]=some [.val (.word heap),.val (.word root),.val (.word (32#64))] := by
    rw [evalListHOLFinite_eq_toExact];simp [evalListHOLExact,evalHOLExact,atH,rootReady]
   have ndKept:=evaluate_avoidsLocal_flowing (ofString "nd") (.call (some (none,none)) (ofString "memcpy")
    [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const (32#64)]) rfl ready (by rw [copyRun];exact Or.inl rfl)
   have hKept:=evaluate_avoidsLocal_flowing (ofString "h") (.call (some (none,none)) (ofString "memcpy")
    [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const (32#64)]) rfl ready (by rw [copyRun];exact Or.inl rfl)
   rw [copyRun] at ndKept hKept
   change copied.locals.lookup (ofString "nd")=ready.locals.lookup (ofString "nd") at ndKept
   change copied.locals.lookup (ofString "h")=ready.locals.lookup (ofString "h") at hKept
   have stored:=evaluate_word_store_normal_memory copied output
    (.op .add [.var .local (ofString "nd"),.const (24#64)]) (.var .local (ofString "h")) (node+24) heap
    (by simp [evalHOLExact,evalListHOLExact,ndKept,nodeReady,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,hKept,atH]) storeRun
   intro watched below
   have separated:=memcpy_interval_separate heap 32 watched aligned fits (Or.inl (by omega))
   have copyFrame:=memcpy_call_normal_memory ready copied _ heap root 32 watched copyArgs (installed.trans code)
    (fun offset inside=>(separated offset inside).1) (fun offset inside=>(separated offset inside).2)
    (by decide) (by rw [clock];change 16≤s.clock-1;omega) copyRun
   have separate : watched≠node+24 := by
    intro equal
    have same:=congrArg BitVec.toNat equal
    have natural : (node+24).toNat=node.toNat+24 := by
     rw [BitVec.toNat_add];change (node.toNat+24)%(2^64)=node.toNat+24
     exact Nat.mod_eq_of_lt (by omega)
    rw [natural] at same
    omega
   rw [postMemory,stored.2 watched separate,copyFrame,memory]
#print axioms decode_witness_attach_hash_normal_memory
end InitECandidate.Runtime
