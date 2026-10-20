import InitECandidate.Runtime.EncodeHeaderPrefixPlan
import InitECandidate.Runtime.EncodeHeaderVariableBytesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def writerInput (index : Nat) : ExpHOL 64 :=
 match encodeHeaderAt index with
 | .seq (.call _ _ args) _ => args[1]?.getD (.const 0)
 | _=>.const 0
def encodeHeaderActualPrefixItems : List (EncodeHeaderPrefixWriter×ExpHOL 64) :=
 [(.bytes 32,writerInput 4),(.bytes 20,writerInput 6),(.bytes 32,writerInput 8),
  (.bytes 32,writerInput 10),(.bytes 32,writerInput 12),(.bytes 256,writerInput 14),
  (.u256,writerInput 16),(.word,writerInput 18),(.word,writerInput 20),
  (.word,writerInput 22),(.word,writerInput 24)]
def encodeHeaderActualPrefixPlanCost : Nat :=
 encodeHeaderPrefixPlanCost encodeHeaderActualPrefixItems encodeHeaderVariableSuffixCost
theorem source_encode_header_actual_prefix_plan :
 encodeHeaderAt 4=encodeHeaderPrefixPlan encodeHeaderActualPrefixItems (encodeHeaderAt 26) := rfl
/-- Concrete original At4 through the variable field and actual return tail.
The length premise is the original retained h136 word, not a callee bound. -/
theorem encode_header_actual_prefix_plan_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap lo length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : (header+136).toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (small : length.toNat≤2^62) (budget : encodeHeaderActualPrefixPlanCost≤s.clock) :
 RunBounded s (encodeHeaderAt 4) encodeHeaderActualPrefixPlanCost := by
 rw [source_encode_header_actual_prefix_plan]
 exact encode_header_prefix_plan_bounded encodeHeaderActualPrefixItems (encodeHeaderAt 26) encodeHeaderVariableSuffixCost
  header heap lo (header+136) length DF cap heapCap heapFence aligned below loHeap
  (by simp [encodeHeaderActualPrefixItems,encodeHeaderPrefixWriterSmall]) (fun next nextValid remaining=>encode_header_variable_suffix_bounded next header heap lo length DF nextValid small remaining)
  s valid budget
#print axioms source_encode_header_actual_prefix_plan
#print axioms encode_header_actual_prefix_plan_bounded
end InitECandidate.Runtime
