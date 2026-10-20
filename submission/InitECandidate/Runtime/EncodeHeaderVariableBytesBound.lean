import InitECandidate.Runtime.EncodeHeaderPrefixInvariant
import InitECandidate.Runtime.EncodeHeaderSource
import InitECandidate.Runtime.EncodeHeaderFixedTailBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def encodeHeaderPrefixField (offset : BitVec 64) : ExpHOL 64 :=
 .load .one (.op .add [.var .local (ofString "h"),.const offset])
def encodeHeaderVariableBytesCost : Nat := rlpEncodeBytesSourceCost (2^62)+1
def encodeHeaderVariableSuffixCost : Nat := encodeHeaderVariableBytesCost+encodeHeaderFixedTailCost
/-- The original variable field is bounded by the retained original h136 word.
An inaccessible h136 rejects during real argument evaluation. -/
theorem encode_header_variable_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap lo length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (small : length.toNat≤2^62) (budget : encodeHeaderVariableSuffixCost≤s.clock) :
 RunBounded s (encodeHeaderAt 26) encodeHeaderVariableSuffixCost := by
 have stage : encodeHeaderAt 26=.seq
  (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes")
   [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]) (encodeHeaderAt 27) := rfl
 rw [stage]
 have callBound : RunBounded s
  (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes")
   [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]) encodeHeaderVariableBytesCost := by
  by_cases readable : s.memaddrs (header+136)
  · have loaded : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (encodeHeaderPrefixField 136)=some (.val (.word length)) := by
     simp [encodeHeaderPrefixField,evalHOLExact,evalListHOLExact,valid.atH,wordOpHOL,wordOp,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
     exact ⟨readable,valid.atLength⟩
    have argsSame : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]=
     evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),encodeHeaderPrefixField 128,.const length] := by
     simp only [evalListHOLFinite_eq_toExact,evalListHOLExact,loaded,evalHOLExact]
    have same : evaluateHOLFiniteState s
      (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes")
       [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136])=
     evaluateHOLFiniteState s
      (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes")
       [.var .local (ofString "p"),encodeHeaderPrefixField 128,.const length]) := by
     simp only [evaluateHOLFiniteState_call,argsSame]
    have mono : rlpEncodeBytesSourceCost length.toNat+1≤encodeHeaderVariableBytesCost := by
     have q32:=Nat.div_le_div_right (c:=32) small
     have q8:=Nat.div_le_div_right (c:=8) small
     unfold encodeHeaderVariableBytesCost rlpEncodeBytesSourceCost
     omega
    have bounded:=ProgBounded.rlpEncodeBytesFixedCall (some (.local,ofString "w"))
     (.var .local (ofString "p")) (encodeHeaderPrefixField 128) length small s valid.code (by unfold encodeHeaderVariableSuffixCost at budget;omega)
    unfold RunBounded at bounded ⊢
    rw [same]
    exact ⟨by have spent:=bounded.1;omega,bounded.2.1,bounded.2.2⟩
  · have failed : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (encodeHeaderPrefixField 136)=none := by
     simp [encodeHeaderPrefixField,evalHOLExact,evalListHOLExact,valid.atH,wordOpHOL,wordOp,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
     exact readable
    have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),encodeHeaderPrefixField 128,encodeHeaderPrefixField 136]=none := by
     rw [evalListHOLFinite_eq_toExact]
     cases firstEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "p")) <;>
      cases secondEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (encodeHeaderPrefixField 128) <;>
      simp only [evalListHOLExact,failed,firstEval,secondEval]
    unfold RunBounded;rw [evaluateHOLFiniteState_call,args];simp
 apply RunBounded.seq callBound budget
 intro next _ sameCode remaining
 exact encode_header_fixed_tail_bounded next (sameCode.trans valid.code) remaining
#print axioms encode_header_variable_suffix_bounded
end InitECandidate.Runtime
