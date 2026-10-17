import InitECandidate.Runtime.JournalRecordSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def journalDeleteRecordSource32 (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
    (.seq (.store (.op .add [.var .local (ofString "r"),.const 8]) (.var .local (ofString "kc")))
      (.seq (.store (.op .add [.var .local (ofString "r"),.const 16]) (.const 1))
        (.seq (.store (.op .add [.var .local (ofString "r"),.const 24]) (.rfield 1 (.var .local (ofString "old")))) continuation)))

def journalDeleteFinish32 : ProgHOL 64 :=
  .seq (.assign .global (ofString "journal_n") (.op .add [.var .global (ofString "journal_n"),.const 1]))
    (.seq (.call (some (none,none)) (ofString "htab_del")
      [.var .local (ofString "t"),.var .local (ofString "key")]) (.return (.const 0)))

def journalDeleteCopy32 : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "memcpy")
    [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")])
    (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
      .panop .mul [.var .global (ofString "journal_n"),.const 32]])
      (journalDeleteRecordSource32 journalDeleteFinish32))

def journalDeletePresent32 : ProgHOL 64 :=
  .seq (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
    (.call (some (none,none)) (ofString "trap_with") [.const 5]) .skip)
    (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"),.const 0]))
      (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalDeleteCopy32))

def journalDeleteAfterGet32 : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip)
    journalDeletePresent32

/-- Exact decomposition of the frozen source, including the checked record
stores, original overflow trap, allocation, copy and set continuation. -/
theorem source_journalDelete32 : sourceFunctionBody Guest.guestFn_jdel =
    .decCall (ofString "old") (.comb [.one,.one]) (ofString "htab_get")
      [.var .local (ofString "t"),.var .local (ofString "key")] journalDeleteAfterGet32 := by
  cbv

#print axioms source_journalDelete32
end InitECandidate.Runtime
