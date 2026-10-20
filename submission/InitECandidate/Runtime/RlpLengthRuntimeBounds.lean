import InitECandidate.Runtime.RlpBeLengthRuntimeBound
import InitECandidate.Runtime.EncGenPrepGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Uniform source ceilings for the actual RLP length helpers. Failed argument
reads and malformed values are included rather than assumed away. -/
theorem rlp_header_length_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_header_len) ((2^64-1)+1) := by
 have tail : ProgBounded (.decCall (ofString "ll") .one (ofString "rlp_be_len")
  [.var .local (ofString "n")] (.return (.op .add [.const 1,.var .local (ofString "ll")])))
  ((2^64-1)+1+0) :=
  ProgBounded.decCall rlp_be_length_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
 have first : ProgBounded (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
  (.return (.const 1)) .skip) 0 := ProgBounded.straight _ rfl
 intro F state code budget
 rw [hlBody_eq]
 have checked:=ProgBounded.seq first tail state code (by simpa only [Nat.zero_add,Nat.add_zero] using budget)
 simpa [hlBody] using checked

theorem rlp_header_length_fun_bounded : FunBounded (ofString "rlp_header_len") ((2^64-1)+1) :=
 ⟨_,_,_,originalRuntimeCode_rlpHeaderLen_lookup,rlp_header_length_body_bounded⟩

theorem rlp_list_header_length_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_list_header_len) (((2^64-1)+1)+1) := by
 intro F state code budget
 rw [lhlBody_eq]
 exact ProgBounded.tail rlp_header_length_fun_bounded [.var .local (ofString "payload_len")] state code budget

theorem rlp_list_header_length_fun_bounded : FunBounded (ofString "rlp_list_header_len") (((2^64-1)+1)+1) :=
 ⟨_,_,_,originalRuntimeCode_rlpListHeaderLen_lookup,rlp_list_header_length_body_bounded⟩

def rlpWordLengthGuard : ProgHOL 64 :=
 match structuralFunctionBody Guest.guestFn_rlp_word_encoded_len with
 | .seq first _=>first
 | _=>.skip

theorem source_rlp_word_length : sourceFunctionBody Guest.guestFn_rlp_word_encoded_len=
 .seq rlpWordLengthGuard (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
  (.return (.op .add [.const 1,.var .local (ofString "ll")]))) := by
 rw [sourceFunctionBody_eq_structural];rfl

theorem rlp_word_length_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_word_encoded_len) ((2^64-1)+1) := by
 have tail : ProgBounded (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
  (.return (.op .add [.const 1,.var .local (ofString "ll")]))) ((2^64-1)+1+0) :=
  ProgBounded.decCall rlp_be_length_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
 have first : ProgBounded rlpWordLengthGuard 0 := ProgBounded.straight _ (by decide_cbv)
 intro F state code budget
 rw [source_rlp_word_length]
 have checked:=ProgBounded.seq first tail state code (by simpa only [Nat.zero_add,Nat.add_zero] using budget)
 simpa [hlBody] using checked

theorem rlp_word_length_fun_bounded : FunBounded (ofString "rlp_word_encoded_len") ((2^64-1)+1) :=
 ⟨_,_,_,originalRuntimeCode_rlpWordEncodedLen_lookup,rlp_word_length_body_bounded⟩
#print axioms rlp_header_length_fun_bounded
#print axioms rlp_list_header_length_fun_bounded
#print axioms rlp_word_length_fun_bounded
end InitECandidate.Runtime
