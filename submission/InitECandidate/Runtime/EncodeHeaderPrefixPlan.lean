import InitECandidate.Runtime.EncodeHeaderPrefixInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def encodeHeaderPrefixWriterCost : EncodeHeaderPrefixWriter→Nat
 | .bytes n=>rlpEncodeBytesSourceCost n.toNat+1
 | .word=>rlpWriterSourceCost+1
 | .u256=>rlpPutU256SourceCost+1
def encodeHeaderPrefixWriterSmall : EncodeHeaderPrefixWriter→Prop
 | .bytes n=>n.toNat≤2^62
 | _=>True
theorem encode_header_prefix_writer_bounded (writer : EncodeHeaderPrefixWriter) (input : ExpHOL 64)
 (small : encodeHeaderPrefixWriterSmall writer) :
 ProgBounded (encodeHeaderPrefixWriterCall writer input) (encodeHeaderPrefixWriterCost writer) := by
 cases writer with
 | bytes n=>exact ProgBounded.rlpEncodeBytesFixedCall _ _ _ n small
 | word=>exact ProgBounded.call rlp_encode_word_fun_bounded _ _
 | u256=>exact ProgBounded.call rlp_put_u256_fun_bounded _ _
def encodeHeaderPrefixIncrement : ProgHOL 64 := .assign .local (ofString "p")
 (.op .add [.var .local (ofString "p"),.var .local (ofString "w")])
def encodeHeaderPrefixPlan (items : List (EncodeHeaderPrefixWriter×ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
 match items with
 | []=>tail
 | item::rest=>.seq (encodeHeaderPrefixWriterCall item.1 item.2) (.seq encodeHeaderPrefixIncrement (encodeHeaderPrefixPlan rest tail))
def encodeHeaderPrefixPlanCost (items : List (EncodeHeaderPrefixWriter×ExpHOL 64)) (tailCost : Nat) : Nat :=
 match items with
 | []=>tailCost
 | item::rest=>encodeHeaderPrefixWriterCost item.1+encodeHeaderPrefixPlanCost rest tailCost
/-- Semantic composition for a finite list of actual writer/increment pairs.
The final use supplies the original variable byte call and original fixed tail. -/
theorem encode_header_prefix_plan_bounded {F : Type} (items : List (EncodeHeaderPrefixWriter×ExpHOL 64))
 (tail : ProgHOL 64) (tailCost : Nat) (header heap lo watched length : BitVec 64) (DF : Nat)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (small : ∀item∈items,encodeHeaderPrefixWriterSmall item.1)
 (last : ∀s : PanSemStateFiniteExact 64 F,EncodeHeaderPrefixInvariant s header heap lo watched length DF→
  tailCost≤s.clock→RunBounded s tail tailCost)
 (s : PanSemStateFiniteExact 64 F) (valid : EncodeHeaderPrefixInvariant s header heap lo watched length DF)
 (budget : encodeHeaderPrefixPlanCost items tailCost≤s.clock) :
 RunBounded s (encodeHeaderPrefixPlan items tail) (encodeHeaderPrefixPlanCost items tailCost) := by
 induction items generalizing s with
 | nil=>exact last s valid budget
 | cons item rest ih=>
  have first:=encode_header_prefix_writer_bounded item.1 item.2 (small item (by simp)) s valid.code
   (by change encodeHeaderPrefixWriterCost item.1+encodeHeaderPrefixPlanCost rest tailCost≤s.clock at budget;omega)
  change RunBounded s (.seq _ (.seq _ _)) (_+_)
  apply RunBounded.seq first budget
  intro middle run sameCode remaining
  obtain ⟨dst,written,increment,nextValid⟩:=encode_header_prefix_writer_advance s middle item.1 item.2 header heap lo watched length DF
   valid cap heapCap heapFence aligned below loHeap run
  have advance : RunBounded middle encodeHeaderPrefixIncrement 0 :=
   ProgBounded.straight _ (by decide_cbv) middle (sameCode.trans valid.code) (Nat.zero_le _)
  have suffix : RunBounded middle (.seq encodeHeaderPrefixIncrement (encodeHeaderPrefixPlan rest tail))
   (0+encodeHeaderPrefixPlanCost rest tailCost) := by
   apply RunBounded.seq advance (by simpa only [Nat.zero_add] using remaining)
   intro next nextRun _ nextBudget
   dsimp only [encodeHeaderPrefixIncrement] at nextRun
   rw [increment] at nextRun
   have equal := (Prod.mk.inj nextRun).2
   subst next
   exact ih (by intro other present;exact small other (by simp [present])) _ nextValid nextBudget
  simpa only [Nat.zero_add] using suffix
#print axioms encode_header_prefix_writer_bounded
#print axioms encode_header_prefix_plan_bounded
end InitECandidate.Runtime
