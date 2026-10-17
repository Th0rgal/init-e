import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original journal record declaration and stores enter any continuation
with the reusable table invariant, without consuming source clock. -/
theorem HashTableReady32.journal_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items journal count journalCapacity savedKey present value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (inside : count.toNat < journalCapacity.toNat)
    (bounded : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (aligned : journal.toNat % 8 = 0)
    (outside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨
      orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (domain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address) :
    ∃ post, HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "r" → post.locals.lookup name = state.locals.lookup name) ∧
      (∀ continuation, evaluateHOLFiniteState state
        (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
          .panop .mul [.var .global (ofString "journal_n"),.const 32]]) (journalRecordSource32 continuation)) =
        (let output := evaluateHOLFiniteState post continuation;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (ofString "r",state.locals.lookup (ofString "r")))}))) := by
  let record := journal + count * 32
  let entered := setVarHOLFinite (ofString "r") (.val (.word record)) state
  let post := journalRecordPost32 entered record table savedKey present value
  have geometry := journal_record_geometry32 journal count journalCapacity inside bounded aligned
  have recordBound : record.toNat + 32 ≤ 33806089496 := by dsimp [record]; omega
  have recordOutside : record.toNat + 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ record.toNat := by
    rcases outside with before | after
    · exact Or.inl (by dsimp [record]; omega)
    · exact Or.inr (by dsimp [record]; omega)
  have entryReady := ready.after_read state entered table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have postReady := entryReady.journal_record entered table pointer keys stride capacity used values order orderPos items record savedKey present value bits recordBound recordOutside
  have locals : ∀ name, name ≠ ofString "r" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨post,postReady,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · exact locals
  · intro continuation
    rw [evaluate_journal_record_scope32 state journal count (journalRecordSource32 continuation) journalGlobal countGlobal]
    have r : entered.locals.lookup (ofString "r") = some (.val (.word record)) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have run := evaluate_journalRecordSource32 entered record table savedKey present value continuation r
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "kc") (by decide)).trans kc)
      ((locals (ofString "old") (by decide)).trans old)
      (journal_record_domains32 state journal count journalCapacity inside bounded aligned domain)
    change (let output := evaluateHOLFiniteState entered (journalRecordSource32 continuation); _) = _
    rw [run]

#print axioms HashTableReady32.journal_scope
end InitECandidate.Runtime
