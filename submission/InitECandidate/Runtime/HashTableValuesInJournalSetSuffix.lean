import InitECandidate.Runtime.HashTableValuesInSetCallAllPlans
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

theorem HashTableReady.journal_set_suffix_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 2 ^ 74 ≤ state.clock)
    (domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) → ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (record savedKey present savedValue journalCount : BitVec 64)
    (before : record.toNat + 32 ≤ table.toNat)
    (recordBound : record.toNat + 32 ≤ 33806089496)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word savedValue)]))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word journalCount)))
    (recordDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (∃ post, evaluateHOLFiniteState state (journalRecordSource32 journalSetFinish32) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ) ∧
      HashTableValuesIn table targets post ∧ state.clock ≤ post.clock + 2 ^ 74 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) ∨
    (let output := evaluateHOLFiniteState state (journalRecordSource32 journalSetFinish32);
      output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ result : ValueHOL 64, output.1 ≠ some (.returned result)) ∧
      output.1 ≠ some .continue ∧ state.clock ≤ output.2.clock + 2 ^ 74 ∧ output.2.clock ≤ state.clock) := by
  let saved := journalRecordPost32 state record table savedKey present savedValue
  have savedReady := initialReady.journal_record_other state keyLength table pointer keys stride capacity used values order orderPos items record table savedKey present savedValue bits recordBound (Or.inl before)
  have savedRegistered := registered.journal_record_before state keyLength table keys stride capacity used values order orderPos items record table savedKey present savedValue bits initialReady.live.arrays targets before
  obtain ⟨middle,increment,middleReady,_,clock,locals,memory,code,addresses,endian⟩ :=
    savedReady.journal_increment saved keyLength table pointer keys stride capacity used values order orderPos items journalCount bits counter
  have middleRegistered := savedRegistered.after_read memory addresses endian
  have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,saved,journalRecordPost32,sourceWriteWord,t,k,v]
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set")
    [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]
  have prefixRun : evaluateHOLFiniteState state (journalRecordSource32 journalSetFinish32) =
      evaluateHOLFiniteState middle (.seq call (.return (.const 0))) := by
    rw [evaluate_journalRecordSource32 state record table savedKey present savedValue _ r t kc old recordDomain]
    change evaluateHOLFiniteState saved (.seq _ (.seq call (.return (.const 0)))) = _
    rw [evaluateHOLFiniteState_seq_line780,increment]
  have outcome := middleReady.set_call_all_plans_values_in middle keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    targets middleRegistered member strideBound (by change middle.clock = state.clock at clock; omega)
    (by intro safe address lower upper; rw [addresses]; exact domain safe address lower upper)
    (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) args capacityLarge keyAligned
    (by simpa only [addresses,saved,journalRecordPost32,sourceWriteWord] using sourceWordDomain) (by simpa only [addresses,saved,journalRecordPost32,sourceWriteWord] using sourceByteDomain)
  rcases outcome with success | failure
  · obtain ⟨post,run,cases,postRegistered,cost,remaining,_,postCode,postAddresses,postEndian⟩ := success
    have returned : evaluateHOLFiniteState post (.return (.const 0)) =
        (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    refine Or.inl ⟨emptyLocalsHOLFinite post,?_,?_,postRegistered.after_read rfl rfl rfl,?_,?_,postCode.trans code,postAddresses.trans addresses,postEndian.trans endian⟩
    · rw [prefixRun]
      exact evaluate_seq_none run returned
    · rcases cases with unchanged | grown
      · obtain ⟨nextCount,counts,valid⟩ := unchanged
        exact Or.inl ⟨nextCount,counts,valid.after_read post _ keyLength table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl⟩
      · exact Or.inr (grown.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
          (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
          (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl)
    · change state.clock ≤ post.clock + 2 ^ 74
      change middle.clock = state.clock at clock
      omega
    · change post.clock ≤ state.clock
      change middle.clock = state.clock at clock
      omega
  · have terminal : evaluateHOLFiniteState middle (.seq call (.return (.const 0))) = evaluateHOLFiniteState middle call := by
      rw [evaluateHOLFiniteState_seq_line780]
      cases resultEq : evaluateHOLFiniteState middle call with
      | mk result post =>
        have nonempty : result ≠ none := by simpa only [call,resultEq] using failure.1
        cases result with
        | none => exact False.elim (nonempty rfl)
        | some result => rfl
    rw [prefixRun,terminal]
    change middle.clock = state.clock at clock
    obtain ⟨nonempty,noTimeout,noReturn,noContinue,cost,remaining⟩ := failure
    change middle.clock ≤ (evaluateHOLFiniteState middle call).2.clock + 2 ^ 74 at cost
    change (evaluateHOLFiniteState middle call).2.clock ≤ middle.clock at remaining
    exact Or.inr ⟨nonempty,noTimeout,noReturn,noContinue,by omega,by omega⟩

#print axioms HashTableReady.journal_set_suffix_values_in
end InitECandidate.Runtime
