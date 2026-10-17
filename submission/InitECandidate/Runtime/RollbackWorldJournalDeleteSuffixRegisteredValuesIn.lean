import InitECandidate.Runtime.RollbackWorldDeleteAppendReservedRegisteredValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteSavedValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteValuesInFamilySmall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original deletion record stores, increment, table deletion and return
establish the enlarged separated world with a uniform source-clock bound. -/
theorem RollbackWorld.journal_delete_suffix_registered_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (r : state.locals.lookup (ofString "r") = some (.val (.word (journal + BitVec.ofNat 64 count.toNat * 32))))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (originalKey : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word originalKey)))
    (originalAligned : originalKey.toNat % 8 = 0)
    (originalWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (originalKey + BitVec.ofNat 64 offset))
    (originalBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (originalKey + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64))
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (registered : table ∈ watched → value ∈ targets)
    (watchedSubset : watched ⊆ tables)
    (tableValues : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (ticks : 2 ^ 42 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (journalDeleteRecordSource32 journalDeleteFinish32) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧ RollbackPhysicalSeparated widths tables post ∧
      JournalSavedValuesIn journal (count + 1).toNat watched targets post ∧
      (∀ other ∈ watched, HashTableValuesIn other targets post) ∧
      state.clock ≤ post.clock + 2 ^ 42 ∧ post.clock ≤ state.clock := by
  obtain ⟨middle,appendRun,midWorld,midSep,midSaved,midValues,clock,locals,domain,code⟩ :=
    world.evaluate_delete_record_append_reserved_registered_values_in separated table key present value member watched targets savedValues registered watchedSubset tableValues space journalBound journalAligned journalHeaders heapDomain
      supported aligned words bytes r t kc old
  have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word originalKey)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,t,keyLocal]
  obtain ⟨post,run,nextWorld,nextSep,postSaved,cost,remaining⟩ := RollbackWorld.registered_delete_saved_values_in middle widths tables journal snapshot (count + 1) table originalKey midWorld midSep member
    supported watched targets midSaved
    (by have nextCount : (count + (1 : BitVec 64)).toNat = count.toNat + 1 := by
          rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]; rfl
        rw [nextCount]; omega)
    (by have nextCount : (count + (1 : BitVec 64)).toNat = count.toNat + 1 := by
          rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]; rfl
        rw [nextCount]; have header := journalHeaders table member; omega)
    (by omega) (.var .local (ofString "t")) (.var .local (ofString "key")) args originalAligned
    (by simpa only [domain] using originalWords) (by simpa only [domain] using originalBytes)
  have postValues := midWorld.registered_delete_values_in_family_small middle widths tables journal snapshot (count + 1) table originalKey midSep member supported
    (by omega) (.var .local (ofString "t")) (.var .local (ofString "key")) args originalAligned
    (by simpa only [domain] using originalWords) (by simpa only [domain] using originalBytes)
    watched targets watchedSubset midValues
  rw [run] at postValues
  refine ⟨post,?_,nextWorld,nextSep,postSaved,postValues,by omega,by omega⟩
  change evaluateHOLFiniteState state (journalDeleteRecordSource32 (.seq (.assign .global (ofString "journal_n")
    (.op .add [.var .global (ofString "journal_n"),.const 1])) _)) = _
  rw [appendRun,evaluateHOLFiniteState_seq_line780,run]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms RollbackWorld.journal_delete_suffix_registered_values_in
end InitECandidate.Runtime
