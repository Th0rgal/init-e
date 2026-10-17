import InitECandidate.Runtime.JournalRecordSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def journalSetFinish32 : ProgHOL 64 :=
  .seq (.assign .global (ofString "journal_n") (.op .add [.var .global (ofString "journal_n"),.const 1]))
    (.seq (.call (some (none,none)) (ofString "htab_set")
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) (.return (.const 0)))

def journalSetCopy32 : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "memcpy")
    [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")])
    (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
      .panop .mul [.var .global (ofString "journal_n"),.const 32]])
      (journalRecordSource32 journalSetFinish32))

def journalSetAfterGet32 : ProgHOL 64 :=
  .seq (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
    (.call (some (none,none)) (ofString "trap_with") [.const 4]) .skip)
    (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"),.const 0]))
      (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32))

/-- Exact decomposition of the frozen source, including the checked record
stores, original overflow trap, allocation, copy and set continuation. -/
theorem source_journalSet32 : sourceFunctionBody Guest.guestFn_jset =
    .decCall (ofString "old") (.comb [.one,.one]) (ofString "htab_get")
      [.var .local (ofString "t"),.var .local (ofString "key")] journalSetAfterGet32 := by
  cbv

#print axioms source_journalSet32
end InitECandidate.Runtime
