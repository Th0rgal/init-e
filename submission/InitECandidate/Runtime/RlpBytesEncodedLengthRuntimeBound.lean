import InitECandidate.Runtime.RlpLengthRuntimeBounds
import InitECandidate.Runtime.OriginalRlpBytesLengthCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def rlpBytesLengthGuard : ProgHOL 64 :=
 match structuralFunctionBody Guest.guestFn_rlp_bytes_encoded_len with
 | .seq first _=>first
 | _=>.skip

theorem source_rlp_bytes_length : sourceFunctionBody Guest.guestFn_rlp_bytes_encoded_len=
 .seq rlpBytesLengthGuard (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
  (.return (.op .add [.var .local (ofString "h"),.var .local (ofString "n")]))) := by
 rw [sourceFunctionBody_eq_structural];rfl

/-- Actual byte-string encoded length, including the single-byte early return
and every failed argument read, with no decoded-length or memory premise. -/
theorem rlp_bytes_length_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_bytes_encoded_len) (((2^64-1)+1)+1) := by
 have tail : ProgBounded (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
  (.return (.op .add [.var .local (ofString "h"),.var .local (ofString "n")]))) (((2^64-1)+1)+1+0) :=
  ProgBounded.decCall rlp_header_length_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
 have first : ProgBounded rlpBytesLengthGuard 0 := ProgBounded.straight _ (by decide_cbv)
 intro F state code budget
 rw [source_rlp_bytes_length]
 have checked:=ProgBounded.seq first tail state code (by simpa only [Nat.zero_add,Nat.add_zero] using budget)
 simpa only [Nat.zero_add,Nat.add_zero] using checked

theorem rlp_bytes_length_fun_bounded : FunBounded (ofString "rlp_bytes_encoded_len") (((2^64-1)+1)+1) :=
 ⟨_,_,_,originalRuntimeCode_rlpBytesEncodedLength_lookup,rlp_bytes_length_body_bounded⟩
#print axioms rlp_bytes_length_fun_bounded
end InitECandidate.Runtime
