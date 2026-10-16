import InitECandidate.Runtime.HashGrowRehashBody
import InitECandidate.Runtime.HashGrowOldSlotDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original rehash iteration using old allocated-array facts and a valid
order entry, with all individual key/value/order read domains derived. -/
theorem evaluate_hashGrow_rehash_body_from_arrays {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count oldKeys oldValues oldOrder oldCapacity slot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word oldOrder)))
    (slotMemory : state.memory (oldOrder + count * 8) = .word slot)
    (countLocal : state.locals.lookup (ofString "k") = some (.val (.word count)))
    (slotInside : slot.toNat < oldCapacity.toNat) (counterInside : count.toNat < oldCapacity.toNat)
    (oldKeysAligned : oldKeys.toNat % 8 = 0) (oldValuesAligned : oldValues.toNat % 8 = 0)
    (oldOrderAligned : oldOrder.toNat % 8 = 0)
    (keyBound : oldKeys.toNat + oldCapacity.toNat * stride.toNat ≤ 33806089496)
    (valueBound : oldValues.toNat + oldCapacity.toNat * 8 ≤ 33806089496)
    (orderBound : oldOrder.toNat + oldCapacity.toNat * 8 ≤ 33806089496)
    (keyDomain : ∀ address : BitVec 64, oldKeys.toNat ≤ address.toNat →
      address.toNat < oldKeys.toNat + oldCapacity.toNat * stride.toNat → state.memaddrs address)
    (valueDomain : ∀ address : BitVec 64, oldValues.toNat ≤ address.toNat →
      address.toNat < oldValues.toNat + oldCapacity.toNat * 8 → state.memaddrs address)
    (orderDomain : ∀ address : BitVec 64, oldOrder.toNat ≤ address.toNat →
      address.toNat < oldOrder.toNat + oldCapacity.toNat * 8 → state.memaddrs address)
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashBody = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state).locals ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨aligned,words,bytes,valueCell⟩ := hashGrow_old_slot_domains state oldKeys stride oldValues oldCapacity slot slotInside
    oldKeysAligned invariant.strideAligned oldValuesAligned invariant.fits keyBound valueBound keyDomain valueDomain
  have interval := hashFind_slot_offset oldOrder count 8 oldCapacity 8 0 counterInside
    (by change oldOrder.toNat + oldCapacity.toNat * 8 ≤ 33806089496; exact orderBound)
    oldOrderAligned (by decide) (by decide) (by decide)
  have orderCell : state.memaddrs (oldOrder + count * 8) := orderDomain _ (by simpa using interval.2.1) (by simpa using interval.2.2)
  exact evaluate_hashGrow_rehash_body state table keys stride capacity used values order orderPos count oldKeys oldValues oldOrder slot bits
    invariant tableLocal keysLocal strideLocal valuesLocal orderLocal orderCell slotMemory countLocal valueCell aligned words bytes roomAfter budget

#print axioms evaluate_hashGrow_rehash_body_from_arrays
end InitECandidate.Runtime
