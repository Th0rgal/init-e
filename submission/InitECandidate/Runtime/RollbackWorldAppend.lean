import InitECandidate.Runtime.TypedJournalRecordAppend
import InitECandidate.Runtime.RollbackRegistryRecord
import InitECandidate.Runtime.RollbackWorldRead
import InitECandidate.Runtime.RollbackPhysicalGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Append the actual four-field record and increment the live journal counter,
retaining the complete world and separated registered-table family. -/
theorem RollbackWorld.append_record {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    let saved := journalRecordPost32 state (journal + BitVec.ofNat 64 count.toNat * 32) table key present value
    let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) saved
    RollbackWorld widths tables journal snapshot (count + 1) post ∧ RollbackPhysicalSeparated widths tables post ∧ post.clock = state.clock := by
  let record := journal + BitVec.ofNat 64 count.toNat * 32
  let saved := journalRecordPost32 state record table key present value
  let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) saved
  have recordAddress : record.toNat = journal.toNat + count.toNat * 32 := address
  have next : (count + 1).toNat = count.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]; rfl
  have prefixBound : journal.toNat + count.toNat * 32 ≤ 33806089496 := by omega
  have records := world.records.after_record state widths journal table key present value count.toNat prefixBound bounded (by omega) supported fields aligned words bytes
  have retained := journalRecordPost32_prefix_frame state journal record table key present value count.toNat prefixBound bounded (by omega)
  obtain ⟨registry,apart⟩ := rollback_registry_after_record state widths tables record table key present value world.ready separated bounded headers
  have family : ∀ other ∈ tables, RollbackTableReady widths other post := by
    intro other belongs
    obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := registry other belongs
    exact ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,
      ready.after_global saved (widths other) other pointer keys stride capacity used values order reverse items bits
        (ofString "journal_n") (.val (.word (count + 1))) (by decide),small,large⟩
  have different : ofString "journal_n" ≠ ofString "journal" := by decide
  have postRecords : TypedJournalUndoRecords widths journal (count + 1).toNat post := by
    rw [next]
    exact records.after_frame (Nat.le_refl _) rfl (by intros; rfl)
  refine ⟨⟨?_,world.snapshotLocal,?_,by omega,postRecords,?_,family,?_⟩,apart.after_global (ofString "journal_n") (.val (.word (count + 1))) (by decide),rfl⟩
  · simp [post,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [post,saved,journalRecordPost32,sourceWriteWord,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using world.journalGlobal
  · intro index inside actualTable cell
    change saved.memory (journal + BitVec.ofNat 64 index * 32) = .word actualTable at cell
    by_cases earlier : index < count.toNat
    · apply world.references index earlier actualTable
      have same := retained index earlier 0 (by simp)
      exact (by simpa using same.symm.trans (by simpa only [BitVec.add_zero,saved] using cell))
    · have same : index = count.toNat := by omega
      subst index
      have atTable := (journalRecordPost32_fields state record table key present value).1
      have tableSame : actualTable = table := HolWordLab.word.inj (cell.symm.trans atTable)
      simpa only [tableSame] using member
  · intro other belongs
    have header := headers other belongs
    rw [next]
    omega

#print axioms RollbackWorld.append_record
end InitECandidate.Runtime
