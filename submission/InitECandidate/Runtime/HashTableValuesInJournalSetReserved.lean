import InitECandidate.Runtime.HashTableValuesInJournalSetScope
import InitECandidate.Runtime.RollbackWorldJournalSetScope
import InitECandidate.Runtime.HashTableValuesInJournalRecord
import InitECandidate.Runtime.HashTableReadyJournal
import InitECandidate.Runtime.HashTableReadyGlobals
import InitECandidate.Runtime.HashTableValuesInSetCallUnsafe
import InitECandidate.Runtime.HashTableValuesInSetCallNoGrowth
import InitECandidate.Runtime.HashTableValuesInSetNoGrowth
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.journal_set_record_reserved_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 2 ^ 74 ≤ state.clock)
    (domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) → ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (journal savedKey present savedValue journalCount : BitVec 64)
    (space : journalCount.toNat < 524288)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalBefore : journal.toNat + 524288 * 32 ≤ table.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + 524288 * 32 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word savedValue)]))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word journalCount)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (∃ post, evaluateHOLFiniteState state journalSetRecordScope32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ) ∧
      HashTableValuesIn table targets post ∧ state.clock ≤ post.clock + 2 ^ 74 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) ∨
    (let output := evaluateHOLFiniteState state journalSetRecordScope32;
      output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ result : ValueHOL 64, output.1 ≠ some (.returned result)) ∧
      output.1 ≠ some .continue ∧ state.clock ≤ output.2.clock + 2 ^ 74 ∧ output.2.clock ≤ state.clock) := by
  have inside : journalCount.toNat < (524288 : BitVec 64).toNat := space
  have bounded : journal.toNat + (524288 : BitVec 64).toNat * 32 ≤ 33806089496 := journalBound
  obtain ⟨_,_,extent⟩ := journal_record_geometry32 journal journalCount 524288 inside bounded journalAligned
  have fields := journal_record_domains32 state journal journalCount 524288 inside bounded journalAligned journalDomain
  exact initialReady.journal_set_record_scope_values_in state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    targets registered member strideBound ticks domain journal savedKey present savedValue journalCount (by omega) (by omega)
    t kc old k v journalGlobal counter fields capacityLarge keyAligned sourceWordDomain sourceByteDomain

#print axioms HashTableReady.journal_set_record_reserved_values_in
end InitECandidate.Runtime
