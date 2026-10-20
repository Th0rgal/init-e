import InitECandidate.Runtime.RlpPutBeRuntimeBound
import InitECandidate.Runtime.RlpBeLengthRuntimeBound
import InitECandidate.Runtime.EncWritersGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Uniform writer ceiling, including arbitrary byte-store failures. -/
def rlpWriterSourceCost : Nat := ((2^64-1)+1)+((2^64-1)+1)
theorem rlp_header_writer_tail_bounded (name : MlS) (value : ExpHOL 64) :
 ProgBounded (hdrTail name value) rlpWriterSourceCost := by
 have returned : ProgBounded (.return (.op .add [.const 1,.var .local (ofString "ll")])) 0 := ProgBounded.straight _ rfl
 have put : ProgBounded (.call (some (none,none)) (ofString "rlp_put_be")
  [.op .add [.var .local (ofString "dst"),.const 1],.var .local name,.var .local (ofString "ll")]) ((2^64-1)+1) :=
  ProgBounded.call rlp_put_be_fun_bounded _ _
 have store : ProgBounded (.storeByte (.var .local (ofString "dst")) value) 0 := ProgBounded.straight _ rfl
 have bound : ProgBounded (hdrTail name value) ((2^64-1)+1+(0+(((2^64-1)+1)+0))) := by
  unfold hdrTail
  exact ProgBounded.decCall rlp_be_length_fun_bounded _ _ _ (ProgBounded.seq store (ProgBounded.seq put returned))
 intro F state code budget
 exact bound state code (by simpa [rlpWriterSourceCost] using budget)

def rlpWriteHeaderGuard : ProgHOL 64 := match whBody with | .seq first _=>first | _=>.skip
def rlpEncodeWordFirst : ProgHOL 64 := match ewBody with | .seq first _=>first | _=>.skip
def rlpEncodeWordSecond : ProgHOL 64 := match ewBody with | .seq _ (.seq second _) =>second | _=>.skip

theorem rlp_write_header_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_write_header) rlpWriterSourceCost := by
 rw [whBody_eq]
 change ProgBounded (.seq rlpWriteHeaderGuard (hdrTail (ofString "n") _)) rlpWriterSourceCost
 intro F state code budget
 have bounded:=ProgBounded.seq (ProgBounded.straight rlpWriteHeaderGuard rfl)
  (rlp_header_writer_tail_bounded (ofString "n") (.op .add [.var .local (ofString "base"),.const (55#64),.var .local (ofString "ll")])) state code (by simpa only [Nat.zero_add] using budget)
 simpa only [Nat.zero_add] using bounded

theorem rlp_write_header_fun_bounded : FunBounded (ofString "rlp_write_header") rlpWriterSourceCost :=
 ⟨_,_,_,originalRuntimeCode_rlpWriteHeader_lookup,rlp_write_header_body_bounded⟩

theorem rlp_encode_word_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_encode_word) rlpWriterSourceCost := by
 rw [ewBody_eq]
 change ProgBounded (.seq rlpEncodeWordFirst (.seq rlpEncodeWordSecond (hdrTail (ofString "w") _))) rlpWriterSourceCost
 intro F state code budget
 have bounded:=ProgBounded.seq (ProgBounded.straight rlpEncodeWordFirst rfl)
  (ProgBounded.seq (ProgBounded.straight rlpEncodeWordSecond rfl)
   (rlp_header_writer_tail_bounded (ofString "w") (.op .add [.const (128#64),.var .local (ofString "ll")]))) state code (by simpa only [Nat.zero_add] using budget)
 simpa only [Nat.zero_add] using bounded

theorem rlp_encode_word_fun_bounded : FunBounded (ofString "rlp_encode_word") rlpWriterSourceCost :=
 ⟨_,_,_,originalRuntimeCode_rlpEncodeWord_lookup,rlp_encode_word_body_bounded⟩

theorem rlp_encode_list_header_body_bounded : ProgBounded
 (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) (rlpWriterSourceCost+1) := by
 rw [sourceFunctionBody_eq_structural]
 change ProgBounded (.call none (ofString "rlp_write_header")
  [.var .local (ofString "dst"),.const 192,.var .local (ofString "payload_len")]) _
 exact ProgBounded.tail rlp_write_header_fun_bounded _

theorem rlp_encode_list_header_fun_bounded : FunBounded (ofString "rlp_encode_list_header") (rlpWriterSourceCost+1) :=
 ⟨_,_,_,originalRuntimeCode_rlpEncodeListHeader_lookup,rlp_encode_list_header_body_bounded⟩
#print axioms rlp_write_header_fun_bounded
#print axioms rlp_encode_word_fun_bounded
#print axioms rlp_encode_list_header_fun_bounded
end InitECandidate.Runtime
