import InitECandidate.Runtime.HashInsertProbeTail
import InitECandidate.Runtime.PtKeyULeafKUGD
/-! Unaligned-key copy of `HashInsertProbeTail` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocated key-slot bounds and domains, independent of its current bytes. -/
structure HashInsertCopyBoundsKU {F : Type} (table keys stride key keyLength used capacity index : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  small : (keys + index * stride).toNat + keyLength.toNat ≤ 33806089496
  aligned : (keys + index * stride).toNat % 8 = 0
  sourceAligned : key.toNat % 8 ≠ 0
  len8 : 8 ≤ keyLength.toNat
  keyFit : key.toNat + keyLength.toNat ≤ 33806089496
  usedAligned : used.toNat % 8 = 0
  headerBefore : table.toNat + 72 ≤ (keys + index * stride).toNat
  copyBefore : (keys + index * stride).toNat + keyLength.toNat ≤ used.toNat
  usedBound : used.toNat + capacity.toNat ≤ 33806089496
  wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset)
  byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))
  sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset)
  sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))




end InitECandidate.Runtime
