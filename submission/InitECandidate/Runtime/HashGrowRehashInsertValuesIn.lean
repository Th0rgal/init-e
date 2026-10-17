import InitECandidate.Runtime.HashGrowRehashInsertMemorySupported
import InitECandidate.Runtime.HashTableValuesInInsertCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original rehash insertion reinserts a registered old value into the
new table and retains membership through its counter advance. -/
theorem evaluate_hashGrow_rehash_insert_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count oldKeys oldValues slot : BitVec 64) (bits frontier : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (slotLocal : state.locals.lookup (ofString "i") = some (.val (.word slot)))
    (countLocal : state.locals.lookup (ofString "k") = some (.val (.word count)))
    (valueDomain : state.memaddrs (oldValues + slot * 8))
    (keyAligned : (oldKeys + slot * stride).toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (oldKeys + slot * stride + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (oldKeys + slot * stride + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (targets : Set (BitVec 64)) (newEntries : HashTableValuesIn table targets state)
    (oldValueRegistered : ∀ value : BitVec 64, state.memory (oldValues + slot * 8) = .word value → value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashInsertAdvance = (none,post) ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state).locals ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier → post.memory watched = state.memory watched) := by
  obtain ⟨post,run,valid,cost,remaining,locals,globals,code,domain,endian,frame⟩ :=
    evaluate_hashGrow_rehash_insert_supported_memory state keyLength table keys stride capacity used values order orderPos count oldKeys oldValues slot bits frontier
      supported invariant beforeKeys beforeValues tableLocal keysLocal strideLocal valuesLocal slotLocal countLocal valueDomain keyAligned
      sourceWordDomain sourceByteDomain roomAfter budget
  obtain ⟨value,valueMemory⟩ : ∃ value : BitVec 64, state.memory (oldValues + slot * 8) = .word value := by
    cases state.memory (oldValues + slot * 8) with | word value => exact ⟨value,rfl⟩
  have arguments := eval_hashGrow_rehash_arguments state table oldKeys stride oldValues slot value
    tableLocal keysLocal strideLocal valuesLocal slotLocal valueDomain valueMemory
  obtain ⟨inserted,insert,_,_,_,_,insertedValues,_,_,_,_,insertedLocals⟩ :=
    evaluate_hashInsert_call_values_in state (.var .local (ofString "t"))
      (.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]])
      (.load .one (hashOrderAddress (ofString "vals") (ofString "i")))
      capacity used table values value order orderPos count keys stride (oldKeys + slot * stride) keyLength bits
      supported budget invariant keyAligned sourceWordDomain sourceByteDomain keysBeforeValues arguments targets newEntries (oldValueRegistered value valueMemory)
  have binding : inserted.locals.lookup (ofString "k") = some (.val (.word count)) := by rw [insertedLocals]; exact countLocal
  have advance := evaluate_hashGrow_rehash_advance inserted count binding
  let checked := setVarHOLFinite (ofString "k") (.val (.word (count + 1))) inserted
  have checkedRun : evaluateHOLFiniteState state hashGrowRehashInsertAdvance = (none,checked) := evaluate_seq_none insert advance
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  refine ⟨post,run,valid,?_,cost,remaining,locals,globals,code,domain,endian,frame⟩
  rw [same]
  exact insertedValues.after_read rfl rfl rfl

#print axioms evaluate_hashGrow_rehash_insert_values_in
end InitECandidate.Runtime
