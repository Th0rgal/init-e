import InitECandidate.Runtime.HashFindIndexWidths
import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HashFindEnvironment {F : Type} (keyLength keys stride key capacity used : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride))
  keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key))
  lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength))
  capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
    address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address
  keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset)
  keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))
  readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte
  room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat

theorem HashFindEnvironment.after_hash {F : Type} (keyLength keys stride key capacity used hash : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F)
    (ready : HashFindEnvironment keyLength keys stride key capacity used state)
    (memory : post.memory = state.memory) (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (locals : post.locals = (setVarHOLFinite (ofString "h") (.val (.word hash)) state).locals) :
    HashFindEnvironment keyLength keys stride key capacity used post := by
  have other : ∀ name, name ≠ ofString "h" → post.locals.lookup name = state.locals.lookup name := by
    intro name different
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨code.trans ready.code,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [other _ (by decide)]; exact ready.keysLocal
  · rw [other _ (by decide)]; exact ready.strideLocal
  · rw [other _ (by decide)]; exact ready.keyLocal
  · rw [other _ (by decide)]; exact ready.lengthLocal
  · rw [other _ (by decide)]; exact ready.capLocal
  · rw [other _ (by decide)]; exact ready.usedLocal
  · rw [addresses]; exact ready.arrayDomain
  · rw [addresses]; exact ready.keyWords
  · rw [addresses]; exact ready.keyBytes
  · rw [memory,addresses,endian]; exact ready.readable
  · have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
      funext index
      unfold hashOccupancyRead
      rw [memory,addresses,endian]
    rw [reads]; exact ready.room


theorem evaluate_hashFindIndexScope20_from_count {F : Type} (table keys stride capacity used values order orderPos count key hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment 20 keys stride key capacity used state)
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
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
  have valid : HashFindInvariant 20 keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyWords,ready.keyBytes,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScope20 table keys stride capacity used values order orderPos count key empty hash
    bits power emptyInside keyAligned state hashLocal ready.capLocal valid arrays budget

theorem evaluate_hashFindIndexScope52_from_count {F : Type} (table keys stride capacity used values order orderPos count key hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment 52 keys stride key capacity used state)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
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
  have valid : HashFindInvariant 52 keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyWords,ready.keyBytes,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScope52 table keys stride capacity used values order orderPos count key empty hash
    bits power emptyInside keyAligned state hashLocal ready.capLocal valid arrays budget

#print axioms HashFindEnvironment.after_hash
#print axioms evaluate_hashFindIndexScope20_from_count
#print axioms evaluate_hashFindIndexScope52_from_count
end InitECandidate.Runtime
