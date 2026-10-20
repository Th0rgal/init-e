import InitECandidate.Runtime.MptInsertCommit
import InitECandidate.Runtime.AllocatedTrieMetadata
import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- In a continuing insertion iteration r is the old current node. Its
previous backlink already stores that node, so the actual commit writes the
same word; the root-local alternative also leaves all memory untouched. -/
theorem mpt_insert_commit_idempotent {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (slot node : BitVec 64)
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word node)))
 (backlink : slot≠0 →s.memory slot=.word node)
 (run : evaluateHOLFiniteState s mptInsertCommit=(none,post)) :
 post.memory=s.memory ∧post.globals=s.globals := by
 have resultEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.var .local (ofString "r"))=some (.val (.word node)) := atResult
 rw [source_mptInsert_commit,evaluateHOLFiniteState_ite] at run
 by_cases zero : slot=0#64
 · have guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "slot")) (.const 0))=some (.val (.word (1#64))) := by
    simp [evalHOLExact,atSlot,zero,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard] at run
   change evaluateHOLFiniteState s (.assign .local (ofString "result") (.var .local (ofString "r")))=(none,post) at run
   rw [evaluateHOLFiniteState_assign,resultEval] at run
   dsimp only at run
   split at run
   · have same : post=setKvarHOLFinite .local (ofString "result") (.val (.word node)) s:=(Prod.mk.inj run).2.symm
     rw [same];exact ⟨rfl,rfl⟩
   · cases run
 · have guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "slot")) (.const 0))=some (.val (.word (0#64))) := by
    simp [evalHOLExact,atSlot,zero,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard] at run
   change evaluateHOLFiniteState s (.store (.var .local (ofString "slot")) (.var .local (ofString "r")))=(none,post) at run
   have same:=store_normal_exact s post (.var .local (ofString "slot")) (.var .local (ofString "r")) slot node atSlot resultEval run
   rw [same]
   constructor
   · funext address
     by_cases sameAddress : address=slot
     · subst address
       simp [sourceWriteWord,backlink zero]
     · simp [sourceWriteWord,sameAddress]
   · rfl

theorem mpt_insert_commit_allocated_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier slot node : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word node)))
 (backlink : slot≠0 →s.memory slot=.word node)
 (run : evaluateHOLFiniteState s mptInsertCommit=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier := by
 obtain ⟨memory,globals⟩:=mpt_insert_commit_idempotent s post slot node atSlot atResult backlink run
 exact world.after_memory_globals memory globals

#print axioms mpt_insert_commit_idempotent
#print axioms mpt_insert_commit_allocated_world
end InitECandidate.Runtime
