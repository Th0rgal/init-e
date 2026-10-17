import InitECandidate.Runtime.HashNewKeysOther32
import InitECandidate.Runtime.HashNewHeaderOther32
import InitECandidate.Runtime.HashTableReadyAllocDeclaration32
import InitECandidate.Runtime.HashNewPrefix
import InitECandidate.Runtime.HashNewKeysAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original hash-table constructor: the heap budget covers every
allocation, and its body returns an empty table within capacity+7 clocks. -/
theorem evaluate_source_htabNew_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 7 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)))
    (otherTable keys otherStride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (otherReady : HashTableReady32 otherTable keys otherStride otherCapacity used values order orderPos items bits table state)
    (earlier : orderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new) =
        (some (.returned (.val (.word table))),post) ∧
      HashTableReady32 otherTable keys otherStride otherCapacity used values order orderPos items bits
        (allocationEnd (allocationEnd (allocationEnd (htabNewUsed table keyLength capacity) capacity) (capacity * 8)) (capacity * 8)) post ∧
      hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ post.clock + capacity.toNat + 7 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have plan := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
  obtain ⟨guard,finish,restSafe⟩ := plan
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 72] =
        some [.val (.word (72 : BitVec 64))] := by rfl
  obtain ⟨allocated,_,allocatedReady,clock,memory,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    otherReady.alloc_declaration state otherTable keys otherStride otherCapacity used values order orderPos items bits table 72 (.const 72) arguments (by omega) guard
  let bound := setVarHOLFinite (ofString "t") (.val (.word table)) allocated
  have nt : ofString "t" ≠ ofString "key_len" := by decide
  have nc : ofString "t" ≠ ofString "cap" := by decide
  have st : ofString "stride" ≠ ofString "t" := by decide
  have sc : ofString "stride" ≠ ofString "cap" := by decide
  have t : bound.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have k : bound.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt,locals] using keyLocal
  have c : bound.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have domain : ∀ offset : Nat, offset ≤ 64 → bound.memaddrs (table + BitVec.ofNat 64 offset) := by
    simpa only [bound,setVarHOLFinite,addresses] using headerDomain
  have prefixRun := evaluate_htabNew_stride_header bound table keyLength capacity htabNewAfterHeader t k c
    (domain 0 (by decide)) (domain 8 (by decide)) (domain 16 (by decide)) (domain 24 (by decide))
  let entered := setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) bound
  let initialized := htabNewHeaderPost entered table keyLength (allocationEnd 0 keyLength) capacity
  have initializedClock : initialized.clock = state.clock - 1 := clock
  have it : initialized.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [initialized,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,st] using t
  have ic : initialized.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [initialized,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,sc] using c
  have stride : initialized.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))) := by
    simp [initialized,htabNewHeaderPost,sourceWriteWord,entered,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have ih : initialized.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd table 72))) := by
    change allocated.globals.lookup _ = _
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredReady := allocatedReady.after_read allocated entered otherTable keys otherStride otherCapacity used values order orderPos items bits (allocationEnd table 72) rfl rfl rfl rfl rfl
  have initializedReady := enteredReady.new_header_other entered otherTable (allocationEnd table 72) keys otherStride otherCapacity used values order orderPos items table keyLength (allocationEnd 0 keyLength) capacity bits (by omega) (Or.inr earlier)
  have layout := htabNew_insertion_layout table keyLength capacity keyBound budget
  dsimp only at layout
  have headerOutside : ∀ offset : Nat, offset ≤ 64 → orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + BitVec.ofNat 64 offset).toNat := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    omega
  obtain ⟨post,tail,preserved,empty,cost,remaining,lastCode,lastAddresses,lastEndian⟩ :=
    evaluate_htabNew_keys_allocation_other initialized table keyLength capacity (postCode.trans code) (by omega)
      ih restSafe keyBound tableAligned budget it ic stride
      (domain 32 (by decide)) (domain 40 (by decide)) (domain 48 (by decide))
      (domain 56 (by decide)) (domain 64 (by decide))
      (by simpa only [initialized,htabNewHeaderPost,sourceWriteWord,entered,bound,setVarHOLFinite,addresses] using wordDomain)
      (by simpa only [initialized,htabNewHeaderPost,sourceWriteWord,entered,bound,setVarHOLFinite,addresses] using byteDomain)
      otherTable keys otherStride otherCapacity used values order orderPos items bits initializedReady (Or.inr (by omega))
      (Or.inr (headerOutside 48 (by decide))) (Or.inr (headerOutside 56 (by decide))) (Or.inr (headerOutside 64 (by decide)))
      (Or.inr (headerOutside 40 (by decide))) (Or.inr (headerOutside 32 (by decide)))
  rw [source_htabNew_header,decl (ofString "t")]
  rw [prefixRun]
  dsimp only
  rw [tail]
  exact ⟨_,rfl,preserved.after_read post _ otherTable keys otherStride otherCapacity used values order orderPos items bits
    (allocationEnd (allocationEnd (allocationEnd (htabNewUsed table keyLength capacity) capacity) (capacity * 8)) (capacity * 8)) rfl rfl rfl rfl rfl,empty,by change state.clock ≤ post.clock + capacity.toNat + 7; omega,
    by change post.clock ≤ state.clock; omega,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian⟩

#print axioms evaluate_source_htabNew_other
end InitECandidate.Runtime
