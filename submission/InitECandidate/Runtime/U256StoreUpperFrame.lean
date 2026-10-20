import InitECandidate.Runtime.RecBeStoreGD
import InitECandidate.Runtime.InterpreterFundingMemoryTransport
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- No byte or aligned-cell window of a concrete nonwrapping buffer ending
below the frontier can hit any word above the frontier. -/
theorem u256_store_window_below (destination watched : BitVec 64) (frontier : Nat)
 (extent : destination.toNat+32≤frontier) (cap : frontier≤2^64)
 (above : frontier≤watched.toNat) : ¬MWin destination 32 watched := by
 rintro ⟨index,small,direct|aligned⟩
 · have natural : (destination+BitVec.ofNat 64 index).toNat=destination.toNat+index := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat];simp only [Nat.mod_eq_of_lt (show index<2^64 by omega)];omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show index<2^64 by omega)]
   have eq:=congrArg BitVec.toNat direct
   rw [natural] at eq
   omega
 · have natural : (destination+BitVec.ofNat 64 index).toNat=destination.toNat+index := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat];simp only [Nat.mod_eq_of_lt (show index<2^64 by omega)];omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show index<2^64 by omega)]
   have lower : (panByteAlignHOL (destination+BitVec.ofNat 64 index)).toNat≤(destination+BitVec.ofNat 64 index).toNat := by rw [byteAlign_toNat];exact Nat.div_mul_le_self _ _
   have eq:=congrArg BitVec.toNat aligned
   rw [natural] at lower
   omega
/-- Actual original 32-byte U256 writer at every outcome/fuel protects all
words above the charged destination extent, including failure prefixes. -/
theorem u256_store_body_upper_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination watched : BitVec 64) (frontier : Nat)
 (extent : destination.toNat+32≤frontier) (cap : frontier≤2^64)
 (above : frontier≤watched.toNat)
 (atDestination : s.locals.lookup (ofString "out")=some (.val (.word destination)))
 (code : s.code=originalRuntimeCode) (domain : DomOK s.memaddrs) :
 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_to_be32)).2.memory watched=s.memory watched := by
 have window:=u256_store_window_below destination watched frontier extent cap above
 have spec:=u2b_wn (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=watched) destination window
 exact (spec F s code ⟨domain,rfl,rfl⟩ trivial (by intro name impossible;exact False.elim impossible) s.globals rfl atDestination).1
#print axioms u256_store_window_below
#print axioms u256_store_body_upper_memory
end InitECandidate.Runtime
