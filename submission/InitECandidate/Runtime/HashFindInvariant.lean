import InitECandidate.Runtime.HashFindLoopRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Lookup bindings and readable memory at the actual source key width. -/
structure HashFindInvariant {F : Type} (keyLength keys stride key capacity used empty : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64) : Prop where
  code : state.code = originalRuntimeCode
  inside : index.toNat < capacity.toNat
  keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride))
  keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key))
  lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength))
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used))
  arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
    address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address
  keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset)
  keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))
  readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte
  emptyLoad : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
    (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + empty) = some 0

/-- Actual iteration effects preserve the concrete lookup invariant on every
continuing probe. No comparison-call behavior is assumed here. -/
theorem HashFindInvariant.preserve {F : Type} (keyLength keys stride key capacity used empty : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F) (index next : BitVec 64)
    (valid : HashFindInvariant keyLength keys stride key capacity used empty state index)
    (inside : next.toNat < capacity.toNat)
    (memory : post.memory = state.memory) (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (locals : post.locals = (setVarHOLFinite (ofString "i") (.val (.word next)) state).locals) :
    HashFindInvariant keyLength keys stride key capacity used empty post next := by
  have other : ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
    intro name different
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨code.trans valid.code,inside,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [other _ (by decide)]; exact valid.keysLocal
  · rw [other _ (by decide)]; exact valid.strideLocal
  · rw [other _ (by decide)]; exact valid.keyLocal
  · rw [other _ (by decide)]; exact valid.lengthLocal
  · rw [locals]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [other _ (by decide)]; exact valid.capLocal
  · rw [other _ (by decide)]; exact valid.usedLocal
  · rw [addresses]; exact valid.arrayDomain
  · rw [addresses]; exact valid.keyWords
  · rw [addresses]; exact valid.keyBytes
  · rw [memory,addresses,endian]; exact valid.readable
  · rw [memory,addresses,endian]; exact valid.emptyLoad


#print axioms HashFindInvariant.preserve
end InitECandidate.Runtime
