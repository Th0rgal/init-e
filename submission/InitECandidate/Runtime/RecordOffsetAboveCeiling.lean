import InitECandidate.Runtime.HeaderWordFieldChainContentFrame
/-!
The record offsets of the header record lie at or above the workspace ceiling.

Every later decoder phase keeps the words of the record it does not write, provided
the written record addresses are at or above the ceiling.  This module records that
geometric fact once: a record offset inside the allocated record is reachable by
`record + ofNat offset` without wrap and is at or above the ceiling.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A record offset that fits the header record is at or above the workspace ceiling
and its bit-vector address has no wrap. -/
theorem record_offset_above_ceiling (array count record : BitVec 64) (ceiling : Nat) (offset : Nat)
    (above : ceiling ≤ array.toNat) (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (offsetBound : offset < 248) (recordFits : record.toNat + 248 < 2^64) :
    ceiling ≤ (record + BitVec.ofNat 64 offset).toNat := by
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have sumNat : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
    rw [BitVec.toNat_add,offsetNat]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  rw [sumNat]
  omega

#print axioms record_offset_above_ceiling
end InitECandidate.Runtime
