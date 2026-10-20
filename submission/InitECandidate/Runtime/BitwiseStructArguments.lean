import InitECandidate.Runtime.BitwiseNotOpcodeSource
import InitECandidate.Runtime.U256ZeroFundingValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Limb combinator of the three direct binary bitwise opcodes. -/
def bitwiseLimb (kind : BitwiseBinaryKind) (p q : BitVec 64) : BitVec 64 :=
 match kind with
 | .and=>p&&&q
 | .or=>p|||q
 | .xor=>p^^^q
/-- Limb complement of the direct NOT opcode. -/
def notLimb (p : BitVec 64) : BitVec 64 := ~~~p
private theorem andOp_eq (p q : BitVec 64) : AndOp.and p q = p&&&q := rfl
private theorem orOp_eq (p q : BitVec 64) : OrOp.or p q = p|||q := rfl
private theorem xorOp_eq (p q : BitVec 64) : XorOp.xor p q = p^^^q := rfl
private theorem and_word (p q : BitVec 64) : p&&&(q&&&(18446744073709551615#64))=p&&&q := by
 rw [show (18446744073709551615#64 : BitVec 64)=BitVec.allOnes 64 from by decide,← BitVec.and_assoc,BitVec.and_allOnes]
private theorem and_eval (p q : BitVec 64) : wordOpHOL BinOp.and [p,q]=some (p&&&q) := by
 simp only [wordOpHOL,wordOp,List.foldr,andOp_eq]
 rw [show (~~~(0 : BitVec 64))=BitVec.allOnes 64 from by decide,← BitVec.and_assoc,BitVec.and_allOnes]
private theorem or_eval (p q : BitVec 64) : wordOpHOL BinOp.or [p,q]=some (p|||q) := by
 simp only [wordOpHOL,wordOp,List.foldr,orOp_eq]
 change some (p|||(q|||(0#64)))=some (p|||q)
 rw [BitVec.or_zero]
private theorem xor_eval (p q : BitVec 64) : wordOpHOL BinOp.xor [p,q]=some (p^^^q) := by
 simp only [wordOpHOL,wordOp,List.foldr,xorOp_eq]
 change some (p^^^(q^^^(0#64)))=some (p^^^q)
 rw [BitVec.xor_zero]
private theorem not_eval (p : BitVec 64) : wordOpHOL BinOp.xor [p,(18446744073709551615#64)]=some (~~~p) := by
 simp only [wordOpHOL,wordOp,List.foldr,xorOp_eq]
 change some (p^^^((18446744073709551615#64)^^^(0#64)))=some (~~~p)
 rw [BitVec.xor_zero,BitVec.xor_comm,show (18446744073709551615#64 : BitVec 64)=BitVec.allOnes 64 from by decide,BitVec.allOnes_xor]
private theorem is_word (p : BitVec 64) : valueIsWord (.val (.word p)) = true := rfl
private theorem word_of (p : BitVec 64) : valueWord (.val (.word p)) = p := rfl
/-- The real direct four-limb struct argument evaluates to the concrete
word-level combination of the two checked popped locals. -/
theorem bitwise_push_args_of_locals {F : Type}
 (kind : BitwiseBinaryKind) (s : PanSemStateFiniteExact 64 F)
 (a b c d e f g h : BitVec 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atY : s.locals.lookup (ofString "y")=some (fundingU256 e f g h)) :
 evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) [bitwisePushValue kind]=
  some [fundingU256 (bitwiseLimb kind a e) (bitwiseLimb kind b f) (bitwiseLimb kind c g) (bitwiseLimb kind d h)] := by
 cases kind
 · simp [bitwisePushValue,bitwiseLimb,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact,atX,atY,and_eval,is_word,word_of]
 · simp [bitwisePushValue,bitwiseLimb,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact,atX,atY,or_eval,is_word,word_of]
 · simp [bitwisePushValue,bitwiseLimb,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact,atX,atY,xor_eval,is_word,word_of]
/-- The real direct NOT struct argument evaluates from the single checked
popped local. -/
theorem not_push_args_of_locals {F : Type}
 (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d)) :
 evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) [notPushValue]=
  some [fundingU256 (notLimb a) (notLimb b) (notLimb c) (notLimb d)] := by
 simp [notPushValue,notLimb,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact,atX,not_eval,is_word,word_of]
#print axioms bitwise_push_args_of_locals
#print axioms not_push_args_of_locals
end InitECandidate.Runtime
