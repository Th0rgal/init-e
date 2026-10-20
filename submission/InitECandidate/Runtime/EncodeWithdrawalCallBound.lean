import InitECandidate.Runtime.EncodeWithdrawalRuntimeBound
import InitECandidate.Runtime.OriginalEncodeWithdrawalCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual installed withdrawal encoder call. No readable withdrawal
 buffer or successful allocator result is assumed. -/
theorem evaluate_encode_withdrawal_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (withdrawal heap : BitVec 64) (DF : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word withdrawal)])
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF+8≤2^62)
 (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496)
 (budget : encodeWithdrawalSourceCost DF+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "encode_withdrawal_rlp") arguments)
  (encodeWithdrawalSourceCost DF+1) := by
 apply RunBounded.call args budget
 intro body callee shape lookup
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "encode_withdrawal_rlp") _ _ body _ shape _ callee
  (by rw [code];exact originalRuntimeCode_encodeWithdrawal_lookup) lookup
 subst same
 exact encode_withdrawal_body_bounded (callEntryStateHOLFinite s callee) heap DF code fence cap heapFence atHeap heapCap
  (by change encodeWithdrawalSourceCost DF≤s.clock-1;omega)
#print axioms evaluate_encode_withdrawal_call_bounded
end InitECandidate.Runtime
