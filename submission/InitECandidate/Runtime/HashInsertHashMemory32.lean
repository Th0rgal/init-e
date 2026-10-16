import InitECandidate.Runtime.HashInsertHashScope32
import InitECandidate.Runtime.HashInsertIndexMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_hash_scope32_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count keys stride key keyLength : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (code : state.code = originalRuntimeCode)
    (width : keyLength = (32 : BitVec 64))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (budget : capacity.toNat + keyLength.toNat + 2 ≤ state.clock)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (environment : HashInsertSlotEnvironment capacity used table values value order orderPos count state)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) (fits : keyLength.toNat ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state hashInsertHashScope = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
          watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧
          watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) →
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
          watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) →
        watched ≠ order + count * 8 → watched ≠ table + 24 → post.memory watched = state.memory watched := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,keyLocal,lengthLocal,width]
  have hashDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    rw [width]
    change offset < 32
    simp at member
    omega
  obtain ⟨hash,hashed,clock,memory,globals,postCode,addresses,endian,locals,decl⟩ :=
    evaluate_hash32_declaration state _ _ key arguments code (by omega) keyAligned hashDomain
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have environmentAfter := HashInsertSlotEnvironment.after_hash capacity used table values value order orderPos count hash state entered
    environment memory addresses endian (by simp only [entered,setVarHOLFinite,locals])
  have other : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have reads : hashOccupancyRead entered used = hashOccupancyRead state used := by
    funext index
    unfold hashOccupancyRead
    rw [show entered.memory = state.memory from memory,show entered.memaddrs = state.memaddrs from addresses,
      show entered.be = state.be from endian]
  have readableAfter : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead entered used current = some byte := by
    rw [reads]; exact readable
  have roomAfter : hashOccupiedCount capacity (hashOccupancyRead entered used) < capacity.toNat := by rw [reads]; exact room
  have arrayAfter : ∀ address : BitVec 64, keys.toNat ≤ address.toNat → address.toNat < keys.toNat + capacity.toNat * stride.toNat → entered.memaddrs address := by
    change ∀ address : BitVec 64, _ → _ → hashed.memaddrs address
    rw [addresses]; exact arrayDomain
  have wordAfter : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (key + BitVec.ofNat 64 offset) := by
    change ∀ offset : Nat, _ → hashed.memaddrs _
    rw [addresses]; exact sourceWordDomain
  have byteAfter : ∀ offset : Nat, offset < keyLength.toNat → entered.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    change ∀ offset : Nat, _ → hashed.memaddrs _
    rw [addresses]; exact sourceByteDomain
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨post,tail,header,agreement,cost,remaining,lastGlobals,lastCode,lastAddresses,lastEndian,lastFrame⟩ := evaluate_hashInsert_index_scope_memory entered capacity used table values value order orderPos count hash
    keys stride key keyLength bits power (postCode.trans code) h
    ((other _ (by decide)).trans capacityLocal) ((other _ (by decide)).trans usedLocal)
    ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
    ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
    (by omega) readableAfter roomAfter environmentAfter keysAligned strideAligned keyAligned usedAligned
    headerBefore keysBefore usedBound fits arrayAfter wordAfter byteAfter
  unfold hashInsertHashScope
  rw [decl]
  change ∃ post, (let output := evaluateHOLFiniteState entered hashInsertIndexScope; _) = _ ∧ _
  rw [tail]
  refine ⟨_,rfl,header,agreement,by change state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2; omega,
    by change post.clock ≤ state.clock; omega,lastGlobals.trans globals,lastCode.trans postCode,
    lastAddresses.trans addresses,lastEndian.trans endian,?_⟩
  intro watched copies stores orderSeparate countSeparate
  have preserved := lastFrame watched copies stores orderSeparate countSeparate
  change post.memory watched = state.memory watched
  rw [preserved]
  change hashed.memory watched = state.memory watched
  rw [memory]

#print axioms evaluate_hashInsert_hash_scope32_memory
end InitECandidate.Runtime
