import InitECandidate.Runtime.RlpFinishListCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- A nonwrapping cursor above the reserved nine-byte prefix gives the real
 list-finisher payload size. No byte-count premise is supplied separately. -/
theorem rlp_finish_list_payload_from_cursor (dst payloadEnd : BitVec 64) (ceiling : Nat)
 (cap : ceiling≤2^62) (afterPrefix : dst.toNat+9≤payloadEnd.toNat) (within : payloadEnd.toNat≤ceiling) :
 (payloadEnd-(dst+9#64)).toNat≤ceiling := by
 have added : (dst+9#64).toNat=dst.toNat+9 := by
  rw [BitVec.toNat_add_of_lt (by change dst.toNat+9<2^64;omega)];rfl
 rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [added];exact afterPrefix)),added]
 omega

/-- The actual call has a uniform ceiling over all cursors inside the arena,
 including every failed memory access and exceptional callee outcome. -/
theorem evaluate_rlp_finish_list_cursor_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (dst payloadEnd : BitVec 64)
 (ceiling : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word dst),.val (.word payloadEnd)])
 (code : s.code=originalRuntimeCode) (cap : ceiling≤2^62)
 (afterPrefix : dst.toNat+9≤payloadEnd.toNat) (within : payloadEnd.toNat≤ceiling)
 (budget : rlpFinishListSourceCost ceiling+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (Flapjack.Basis.Pure.MlString.ofString "rlp_finish_list") arguments)
  (rlpFinishListSourceCost ceiling+1) := by
 have lengthBound:=rlp_finish_list_payload_from_cursor dst payloadEnd ceiling cap afterPrefix within
 have costBound : rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat+1≤rlpFinishListSourceCost ceiling+1 := by
  unfold rlpFinishListSourceCost rlpFinishListTailCost
  omega
 exact (evaluate_rlp_finish_list_call_bounded s destination arguments dst payloadEnd args code
  (lengthBound.trans cap) (costBound.trans budget)).weaken costBound
#print axioms rlp_finish_list_payload_from_cursor
#print axioms evaluate_rlp_finish_list_cursor_bounded
end InitECandidate.Runtime
