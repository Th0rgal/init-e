import InitECandidate.Runtime.PtKeyUFindTableGD
import InitECandidate.Runtime.PtKeyUCopyFrameGD
import InitECandidate.Runtime.HashTableArraysFindSupported
import InitECandidate.Runtime.HashCallSupported
/-!
Unaligned-key (`KU`) leaves for the set/insert chain, with the argument conventions of the generated `KU` copies: a key
alignment premise `key % 8 = 0` becomes `key % 8 ≠ 0` followed by `8 ≤ keyLength` and the key fit
`key + keyLength ≤ 33806089496`.  The lookup budget `2·cap + 2` becomes the linear `54·cap + 2` (width ≤ 52).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.find_supportedKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 54 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      state.clock ≤ ready.clock + 54 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have small : keyLength.toNat ≤ 52 := by rcases supported with rfl | rfl | rfl <;> decide
  have scaled := Nat.mul_le_mul_right capacity.toNat (show keyLength.toNat + 2 ≤ 54 by omega)
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,arrays,decl⟩ :=
    invariant.findK state keyLength table keys stride capacity used values order orderPos count key bits
      tableArgument keyArgument arguments supported keyFit keyWords keyBytes (by omega)
  exact ⟨found,ready,inside,by omega,remaining,memory,globals,code,addresses,endian,locals,arrays,decl⟩

theorem evaluate_hash_supported_declarationKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointerArgument lengthArgument : ExpHOL 64) (pointer keyLength : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [pointerArgument,lengthArgument] =
        some [.val (.word pointer),.val (.word keyLength)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : pointer.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : pointer.toNat + keyLength.toNat ≤ 33806089496)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (words : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.locals = state.locals ∧ ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_hash") [pointerArgument,lengthArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) :=
  evaluate_hashK_declaration state pointerArgument lengthArgument pointer keyLength arguments code clock supported keyFit bytes

/-- The source operand is unaligned while the destination slot is aligned. -/
theorem unal_of_dst_aligned {d s : BitVec 64} (hd : d.toNat % 8 = 0) (hs : s.toNat % 8 ≠ 0) : (d ||| s) &&& 7 ≠ 0 := by
  intro h
  have m : ((d ||| s) &&& 7).toNat = 0 := by rw [h]; rfl
  simp only [BitVec.toNat_and, BitVec.toNat_or] at m
  change (d.toNat ||| s.toNat) &&& (2 ^ 3 - 1) = 0 at m
  rw [Nat.and_two_pow_sub_one_eq_mod] at m
  apply hs
  have hsd : s.toNat % 8 = (d.toNat ||| s.toNat) % 8 % 8 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod s.toNat 3, ← Nat.and_two_pow_sub_one_eq_mod (d.toNat ||| s.toNat) 3]
    rw [← Nat.and_two_pow_sub_one_eq_mod _ 3]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 3
    · have : d.toNat.testBit i = false := by
        have := Nat.testBit_mod_two_pow d.toNat 3 i
        rw [show d.toNat % 2 ^ 3 = 0 by omega] at this
        simp at this
        simp [this, hi]
      simp [this, hi]
    · simp [hi]
  omega

theorem evaluate_memcpy_aligned_call_with_frameKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64)
    (destination source size capacity used : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 ≠ 0) (len8 : 8 ≤ size.toNat)
    (keyFit : source.toNat + size.toNat ≤ 33806089496) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word destination),.val (.word source),.val (.word size)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      ∀ watched : BitVec 64,
        (∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset) →
        (∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
        post.memory watched = state.memory watched :=
  evaluate_memcpy_unaligned_call_with_frame state destinationArgument sourceArgument sizeArgument destination source size
    capacity used small (unal_of_dst_aligned aligned sourceAligned) len8 budget byteDomain sourceByteDomain byteSeparate
    code arguments

#print axioms HashTableArraysInvariant.find_supportedKU
#print axioms evaluate_hash_supported_declarationKU
#print axioms unal_of_dst_aligned
#print axioms evaluate_memcpy_aligned_call_with_frameKU
end InitECandidate.Runtime
