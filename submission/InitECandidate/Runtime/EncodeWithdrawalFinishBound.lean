import InitECandidate.Runtime.RlpFinishListCursorBound
import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Spine of the actual withdrawal encoder, retaining its real SSZ reads. -/
def encodeWithdrawalAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_encode_withdrawal_rlp)
def encodeWithdrawalFinishCost (ceiling : Nat) : Nat := rlpFinishListSourceCost ceiling+1

theorem source_encode_withdrawal_finish : encodeWithdrawalAt 10=
 .decCall (ofString "total") .one (ofString "rlp_finish_list")
 [.var .local (ofString "buf"),.var .local (ofString "p")] (encodeWithdrawalAt 11) := rfl

/-- The real final declaration and return are bounded from the cursor geometry
 produced by the field writers; failed memory operations are included. -/
theorem encode_withdrawal_finish_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (buffer cursor : BitVec 64) (ceiling : Nat)
 (atBuffer : s.locals.lookup (ofString "buf")=some (.val (.word buffer)))
 (atCursor : s.locals.lookup (ofString "p")=some (.val (.word cursor)))
 (code : s.code=originalRuntimeCode) (cap : ceiling≤2^62)
 (afterPrefix : buffer.toNat+9≤cursor.toNat) (within : cursor.toNat≤ceiling)
 (budget : encodeWithdrawalFinishCost ceiling≤s.clock) :
 RunBounded s (encodeWithdrawalAt 10) (encodeWithdrawalFinishCost ceiling) := by
 rw [source_encode_withdrawal_finish]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "buf"),.var .local (ofString "p")]=some [.val (.word buffer),.val (.word cursor)] := by
  simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atBuffer,atCursor]
 have lengthBound:=rlp_finish_list_payload_from_cursor buffer cursor ceiling cap afterPrefix within
 have costBound : rlpFinishListSourceCost (cursor-(buffer+9#64)).toNat≤rlpFinishListSourceCost ceiling := by
  unfold rlpFinishListSourceCost rlpFinishListTailCost
  omega
 have endBound : ProgBounded (encodeWithdrawalAt 11) 0 := ProgBounded.straight _ (by decide_cbv)
 suffices bounded : RunBounded s
  (.decCall (ofString "total") .one (ofString "rlp_finish_list")
   [.var .local (ofString "buf"),.var .local (ofString "p")] (encodeWithdrawalAt 11))
  (rlpFinishListSourceCost ceiling+1+0) by
  simpa only [Nat.add_zero,encodeWithdrawalFinishCost] using bounded
 apply RunBounded.decCall args (by simpa only [Nat.add_zero,encodeWithdrawalFinishCost] using budget)
 intro body callee shape lookup
 have found:=pan_two_word_lookup s.code.lookup (ofString "rlp_finish_list") (ofString "dst") (ofString "payload_end")
  (sourceFunctionBody Guest.guestFn_rlp_finish_list) buffer cursor (by decide)
  (by rw [code];exact originalRuntimeCode_rlpFinishList_lookup)
 rw [found] at lookup
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj lookup |>.symm
 let entry:=callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word buffer))).update
  (ofString "payload_end",.val (.word cursor)))
 have bodyBound:=rlp_finish_list_body_bounded entry buffer cursor
  (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) code (lengthBound.trans cap)
  (by change rlpFinishListSourceCost (cursor-(buffer+9#64)).toNat≤s.clock-1
      unfold encodeWithdrawalFinishCost at budget
      omega)
 refine ⟨bodyBound.weaken costBound,?_⟩
 intro value post returned remaining
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_finish_list)
 rw [returned] at metadata
 exact endBound _ (metadata.1.trans code) remaining
#print axioms encode_withdrawal_finish_bounded
end InitECandidate.Runtime
