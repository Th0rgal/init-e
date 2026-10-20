import InitECandidate.Runtime.MptInsertCommitIdempotent
import InitECandidate.Runtime.MptInsertFinish
import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.EncodeHeaderNormalPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual next-node/backlink/level assignments write no memory or globals,
including when a source assignment rejects an invalid local shape. -/
theorem mpt_insert_advance_memory_frame : MemoryFrame mptInsertAdvance :=
 memoryFrame_leaf _ (by rw [source_mptInsert_advance];rfl)

/-- The whole actual finishing suffix of a continuing iteration is memory
idempotent: commit the already-present backlink, then copy prepared locals. -/
theorem mpt_insert_finish_idempotent {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (slot node : BitVec 64)
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word node)))
 (backlink : slot≠0 →s.memory slot=.word node) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptInsertFinish=(none,post)) :
 post.memory=s.memory ∧post.globals=s.globals := by
 rw [source_mptInsert_finish] at run
 obtain ⟨committed,commitRun,advanceRun⟩:=encode_header_seq_normal s post _ _ run
 obtain ⟨memory,globals⟩:=mpt_insert_commit_idempotent s committed slot node atSlot atResult backlink commitRun
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertCommit
 rw [commitRun] at metadata
 have advanceFrame:=mpt_insert_advance_memory_frame committed (metadata.1.trans code)
 rw [advanceRun] at advanceFrame
 exact ⟨advanceFrame.1.trans memory,advanceFrame.2.trans globals⟩

theorem mpt_insert_finish_allocated_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier slot node : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word node)))
 (backlink : slot≠0 →s.memory slot=.word node) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptInsertFinish=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier := by
 obtain ⟨memory,globals⟩:=mpt_insert_finish_idempotent s post slot node atSlot atResult backlink code run
 exact world.after_memory_globals memory globals

#print axioms mpt_insert_advance_memory_frame
#print axioms mpt_insert_finish_idempotent
#print axioms mpt_insert_finish_allocated_world
end InitECandidate.Runtime
