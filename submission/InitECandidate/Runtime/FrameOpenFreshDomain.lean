import InitECandidate.Runtime.FrameNewDeclarationFunding
import InitECandidate.Runtime.ScratchAllocationGeometry
import InitECandidate.Runtime.AllocationRoundNoWrap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxHeartbeats 2000000
/-- The concrete expanded address domain supplies fresh scratch byte words
from size-fit alone; no allocation-room assumption is needed. -/
theorem frame_open_fresh_scratch_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer size : BitVec 64) (fits : size.toNat≤pointer.toNat) (cap : pointer.toNat≤33806089496)
 (domain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (offset : Nat) (inside : offset<size.toNat) :
 s.memaddrs (panByteAlignHOL (scratchAllocationEnd pointer size+BitVec.ofNat 64 offset)) := by
 have cover:=scratchAllocationEnd_before pointer size fits
 have offsetSmall : offset<2^64:=by have:=size.isLt;omega
 have offsetNat : (BitVec.ofNat 64 offset).toNat=offset:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
 have addBound : (scratchAllocationEnd pointer size).toNat+(BitVec.ofNat 64 offset).toNat<2^64:=by rw [offsetNat];omega
 apply domain
 rw [byteAlign_toNat,BitVec.toNat_add_of_lt addBound,offsetNat]
 have alignBound:=Nat.div_mul_le_self ((scratchAllocationEnd pointer size).toNat+offset) 8
 omega
#print axioms frame_open_fresh_scratch_domain
end InitECandidate.Runtime
