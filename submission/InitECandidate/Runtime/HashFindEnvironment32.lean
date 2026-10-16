import InitECandidate.Runtime.HashFindIndex32
import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Table conditions before introducing the probe index. The occupancy count
supplies an empty slot instead of requiring a separately chosen witness. -/
structure HashFindEnvironment32 {F : Type} (keys stride key capacity used : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride))
  keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key))
  lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64)))
  capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
    address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address
  keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset)
  readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte
  room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat

theorem evaluate_hashFindIndexScope32_from_count {F : Type} (keys stride key capacity used hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment32 keys stride key capacity used state)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨empty,emptyInside,emptyLoad⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used) ready.room
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have valid : HashFindInvariant32 keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyDomain,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScope32 keys stride key capacity used empty hash bits power emptyInside keysAligned strideAligned
    keyAligned strideFits bounded state hashLocal ready.capLocal valid budget

#print axioms evaluate_hashFindIndexScope32_from_count
end InitECandidate.Runtime
