import InitECandidate.Runtime.HashFindLoopRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete locals and memory conditions maintained by a32-byte key lookup. -/
structure HashFindInvariant32 {F : Type} (keys stride key capacity used empty : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64) : Prop where
  code : state.code = originalRuntimeCode
  inside : index.toNat < capacity.toNat
  keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride))
  keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key))
  lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64)))
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
    address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address
  keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset)
  readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte
  emptyLoad : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
    (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + empty) = some 0

/-- Actual iteration effects preserve the concrete lookup invariant on every
continuing probe. No comparison-call behavior is assumed here. -/
theorem HashFindInvariant32.preserve {F : Type} (keys stride key capacity used empty : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F) (index next : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (inside : next.toNat < capacity.toNat)
    (memory : post.memory = state.memory) (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (locals : post.locals = (setVarHOLFinite (ofString "i") (.val (.word next)) state).locals) :
    HashFindInvariant32 keys stride key capacity used empty post next := by
  have other : ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
    intro name different
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨code.trans valid.code,inside,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [other _ (by decide)]; exact valid.keysLocal
  · rw [other _ (by decide)]; exact valid.strideLocal
  · rw [other _ (by decide)]; exact valid.keyLocal
  · rw [other _ (by decide)]; exact valid.lengthLocal
  · rw [locals]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [other _ (by decide)]; exact valid.capLocal
  · rw [other _ (by decide)]; exact valid.usedLocal
  · rw [addresses]; exact valid.arrayDomain
  · rw [addresses]; exact valid.keyDomain
  · rw [memory,addresses,endian]; exact valid.readable
  · rw [memory,addresses,endian]; exact valid.emptyLoad

/-- Complete actual lookup-loop bound for aligned32-byte keys in a readable
power-of-two table with a known empty slot. -/
theorem evaluate_hashFindLoop32 {F : Type} (keys stride key capacity used empty : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (budget : 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant32 keys stride key capacity used empty post finalIndex) ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  apply evaluate_hashFindLoop_rank capacity empty used bits power emptyInside
    (HashFindInvariant32 keys stride key capacity used empty)
    (fun _ _ h => ⟨h.indexLocal,h.usedLocal⟩)
    (fun _ _ h => h.readable _ h.inside) (fun _ _ h => h.emptyLoad) ?_
    _ state index valid valid.inside rfl budget
  intro current probe byte h inside enough loaded occupied
  obtain ⟨result,post,run,outcome,ticks,memory,globals,code,addresses,endian,_,locals⟩ :=
    evaluate_hashFind_occupied32 current keys stride key probe capacity used byte h.code enough
      keysAligned strideAligned keyAligned strideFits inside bounded h.arrayDomain h.keyDomain
      h.keysLocal h.strideLocal h.keyLocal h.lengthLocal h.indexLocal h.capLocal h.usedLocal loaded occupied
  refine ⟨result,post,?_,outcome,ticks,?_,memory,globals,code,addresses,endian⟩
  · cases result <;> exact run
  · intro continuing
    have nextInside : (hashProbeNext probe capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat probe capacity bits power inside]
      apply Nat.mod_lt
      rw [power]; exact Nat.two_pow_pos bits
    exact HashFindInvariant32.preserve keys stride key capacity used empty current post probe _ h nextInside memory code addresses endian (locals continuing)

theorem evaluate_hashFindLoop32_capacity {F : Type} (keys stride key capacity used empty : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant32 keys stride key capacity used empty post finalIndex) ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have rankBound := hashProbeDistance_lt_capacity capacity.toNat index.toNat empty.toNat valid.inside emptyInside
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩ := evaluate_hashFindLoop32 keys stride key capacity used empty bits
    power emptyInside keysAligned strideAligned keyAligned strideFits bounded state index valid (by omega)
  exact ⟨result,post,run,by omega,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩

#print axioms evaluate_hashFindLoop32_capacity
#print axioms HashFindInvariant32.preserve
#print axioms evaluate_hashFindLoop32
end InitECandidate.Runtime
