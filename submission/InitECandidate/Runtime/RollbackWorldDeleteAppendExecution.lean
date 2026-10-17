import InitECandidate.Runtime.RollbackWorldAppend
import InitECandidate.Runtime.JournalDeleteRecord32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original four local-expression stores and global increment.
Any continuation starts in the enlarged world with no source-clock cost. -/
theorem RollbackWorld.evaluate_delete_record_append {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key present value : BitVec 64) (member : table ∈ tables)
    (space : count.toNat < 524288)
    (address : (journal + BitVec.ofNat 64 count.toNat * 32).toNat = journal.toNat + count.toNat * 32)
    (bounded : (journal + BitVec.ofNat 64 count.toNat * 32).toNat + 32 ≤ 33806089496)
    (headers : ∀ other ∈ tables, (journal + BitVec.ofNat 64 count.toNat * 32).toNat + 32 ≤ other.toNat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (fields : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + BitVec.ofNat 64 count.toNat * 32 + BitVec.ofNat 64 offset))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word (journal + BitVec.ofNat 64 count.toNat * 32))))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)])) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state
      (journalDeleteRecordSource32 (.seq (.assign .global (ofString "journal_n")
        (.op .add [.var .global (ofString "journal_n"),.const 1])) continuation)) =
      evaluateHOLFiniteState post continuation) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧
      RollbackPhysicalSeparated widths tables post ∧ post.clock = state.clock ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.code = state.code := by
  let saved := journalRecordPost32 state (journal + BitVec.ofNat 64 count.toNat * 32) table key 1 value
  let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) saved
  obtain ⟨nextWorld,nextSeparated,clock⟩ := world.append_record separated table key 1 value member space address bounded headers supported fields aligned words bytes
  refine ⟨post,?_,nextWorld,nextSeparated,clock,rfl,rfl,rfl⟩
  intro continuation
  rw [evaluate_journalDeleteRecordSource32 state _ table key present value _ r t kc old fields]
  have counter : saved.globals.lookup (ofString "journal_n") = some (.val (.word count)) := world.counter
  have increment : evaluateHOLFiniteState saved (.assign .global (ofString "journal_n")
      (.op .add [.var .global (ofString "journal_n"),.const 1])) = (none,post) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,counter,wordOpHOL,wordOp,valueIsWord,valueWord,
      isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,post]
  change evaluateHOLFiniteState saved (.seq _ continuation) = _
  rw [evaluateHOLFiniteState_seq_line780,increment]

#print axioms RollbackWorld.evaluate_delete_record_append
end InitECandidate.Runtime
