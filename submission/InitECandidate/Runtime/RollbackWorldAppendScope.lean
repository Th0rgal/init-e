import InitECandidate.Runtime.RollbackWorldAppendReserved
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original computed record declaration, stores and increment reach an
 enlarged world, restoring the caller's r binding after any continuation. -/
theorem RollbackWorld.evaluate_record_scope_append {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key present value : BitVec 64) (member : table ∈ tables)
    (space : count.toNat < 524288)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)])) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state
      (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
        .panop .mul [.var .global (ofString "journal_n"),.const 32]])
        (journalRecordSource32 (.seq (.assign .global (ofString "journal_n")
          (.op .add [.var .global (ofString "journal_n"),.const 1])) continuation))) =
      (let output := evaluateHOLFiniteState post continuation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "r",state.locals.lookup (ofString "r"))}))) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧
      RollbackPhysicalSeparated widths tables post ∧ post.clock = state.clock ∧
      post.locals = (setVarHOLFinite (ofString "r") (.val (.word (journal + count * 32))) state).locals ∧
      post.memaddrs = state.memaddrs ∧ post.code = state.code := by
  let entered := setVarHOLFinite (ofString "r") (.val (.word (journal + count * 32))) state
  have enteredWorld : RollbackWorld widths tables journal snapshot count entered :=
    world.after_read rfl rfl rfl rfl rfl (by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "snap" from by decide])
  have enteredSep : RollbackPhysicalSeparated widths tables entered := separated.after_read rfl rfl rfl rfl rfl
  have atR : entered.locals.lookup (ofString "r") = some (.val (.word (journal + BitVec.ofNat 64 count.toNat * 32))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atT : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "t" from by decide] using t
  have atKc : entered.locals.lookup (ofString "kc") = some (.val (.word key)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "kc" from by decide] using kc
  have atOld : entered.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "old" from by decide] using old
  obtain ⟨post,run,nextWorld,nextSep,clock,locals,domain,code⟩ :=
    enteredWorld.evaluate_record_append_reserved enteredSep table key present value member space journalBound journalAligned journalHeaders heapDomain
      supported aligned words bytes atR atT atKc atOld
  refine ⟨post,?_,nextWorld,nextSep,clock,locals,domain,code⟩
  intro continuation
  rw [evaluate_journal_record_scope32 state journal count _ world.journalGlobal world.counter]
  change (let output := evaluateHOLFiniteState entered (journalRecordSource32 (.seq (.assign .global (ofString "journal_n") (.op .add [.var .global (ofString "journal_n"),.const 1])) continuation)); _) = _
  rw [run]

#print axioms RollbackWorld.evaluate_record_scope_append
end InitECandidate.Runtime
