import InitECandidate.Runtime.HashTableValuesInJournalSetSuffix
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

theorem HashTableReady.journal_set_record_scope_values_in {F : Type}
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
    (before : (journal + journalCount * 32).toNat + 32 ≤ table.toNat)
    (recordBound : (journal + journalCount * 32).toNat + 32 ≤ 33806089496)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word savedValue)]))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word journalCount)))
    (recordDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + journalCount * 32 + BitVec.ofNat 64 offset))
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
  let entered := setVarHOLFinite (ofString "r") (.val (.word (journal + journalCount * 32))) state
  have entryReady := initialReady.after_read state entered keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have entryRegistered := registered.after_read (post := entered) rfl rfl rfl
  have atR : entered.locals.lookup (ofString "r") = some (.val (.word (journal + journalCount * 32))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atT : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "t" from by decide] using t
  have atKc : entered.locals.lookup (ofString "kc") = some (.val (.word savedKey)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "kc" from by decide] using kc
  have atOld : entered.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word savedValue)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "old" from by decide] using old
  have atKey : entered.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "key" from by decide] using k
  have atValue : entered.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "value" from by decide] using v
  have scopeRun : evaluateHOLFiniteState state journalSetRecordScope32 =
      (let output := evaluateHOLFiniteState entered (journalRecordSource32 journalSetFinish32);
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "r",state.locals.lookup (ofString "r"))})) :=
    evaluate_journal_record_scope32 state journal journalCount _ journalGlobal counter
  have outcome := entryReady.journal_set_suffix_values_in entered keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    targets entryRegistered member strideBound ticks domain (journal + journalCount * 32) savedKey present savedValue journalCount before recordBound
    atR atT atKc atOld atKey atValue counter recordDomain capacityLarge keyAligned sourceWordDomain sourceByteDomain
  rcases outcome with success | failure
  · obtain ⟨post,run,cases,postRegistered,cost,remaining,code,addresses,endian⟩ := success
    rw [scopeRun,run]
    refine Or.inl ⟨_,rfl,?_,postRegistered.after_read rfl rfl rfl,cost,remaining,code,addresses,endian⟩
    rcases cases with unchanged | grown
    · obtain ⟨nextCount,counts,valid⟩ := unchanged
      exact Or.inl ⟨nextCount,counts,valid.after_read post _ keyLength table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl⟩
    · exact Or.inr (grown.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
        (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl)
  · exact Or.inr (by simpa only [scopeRun,entered,setVarHOLFinite] using failure)

#print axioms HashTableReady.journal_set_record_scope_values_in
end InitECandidate.Runtime
