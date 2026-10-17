import InitECandidate.Runtime.HashTableReadyGrowPhysicalSupported
import InitECandidate.Runtime.HashTableReadyInsertPhysicalSupported
import InitECandidate.Runtime.HashSetGrowthTrue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original missing-key growth and insertion preserve both reusable tables. -/
theorem HashTableReady.set_missing_growth_supported_with_physical_table {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (above : capacity.toNat < (items.toNat + 1) * 2) (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      state.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have capBound : capacity.toNat ≤ 33806089496 := by
    have u := ready.live.arrays.usedBefore
    have o := ready.live.arrays.orderBefore
    have e := ready.live.arrays.endBound
    omega
  have selected := evaluate_hashSet_growth_selected state table capacity items t
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 16 (by decide)) ready.live.arrays.cell16
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 24 (by decide)) ready.live.arrays.cell24
    above ready.live.arrays.room capBound
  have growArguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t")] = some [.val (.word table)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t]
  obtain ⟨grown,grow,grownReady,grownOther,growCost,growRemaining,locals,code,addresses,endian⟩ :=
    ready.grow_supported_with_physical_table state keyLength table pointer keys stride capacity used values order orderPos items bits supported
      (.var .local (ofString "t")) growArguments strideBound safePlan (by omega) domain
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady (by
        intro address lower upper
        exact separate address (Or.inl ⟨lower,upper⟩))
  have arguments : evalListHOLFinite grown (h := fun address => Classical.propDecidable (grown.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,t,k,v]
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 :=
    BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have room := ready.live.arrays.room
  have grownSeparate : ∀ address : BitVec 64,
      tablePhysicalRegion table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address := by
    intro address member otherMember
    have below := otherReady.physical_below_frontier state otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits address otherMember
    have ku := grownReady.live.arrays.keysBefore
    have uo := grownReady.live.arrays.usedBefore
    have oo := grownReady.live.arrays.orderBefore
    have kv := grownReady.ordering
    rcases member with header | arrays
    · exact separate address (Or.inl header) otherMember
    · unfold tablePhysicalRegion at *
      omega
  obtain ⟨post,insert,postReady,postOther,insertCost,insertRemaining,_,_,postAddresses,postEndian⟩ :=
    grownReady.insert_supported_with_physical_disjoint_table grown keyLength table (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) pointer stride (capacity * 2)
      (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      items key value (bits + 1) supported (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) arguments keyAligned
      (by rw [addresses]; exact sourceWordDomain) (by rw [addresses]; exact sourceByteDomain) (by rw [doubled]; omega) (by omega)
      otherKeyLength otherTable (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
      grownOther grownSeparate
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite post,?_,
    postReady.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride)
      (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl,
    postOther.after_read post _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl,
    ?_,?_,postReady.live.arrays.code.trans ready.live.arrays.code.symm,postAddresses.trans addresses,postEndian.trans endian⟩
  · rw [source_hashSet_missing]
    exact evaluate_seq_none (selected.trans grow) (evaluate_seq_none insert returned)
  · change state.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady.set_missing_growth_supported_with_physical_table
end InitECandidate.Runtime
