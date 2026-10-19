import InitECandidate.Runtime.MptReadFrame
import InitECandidate.Runtime.OriginalRlpFailCode
import InitECandidate.Runtime.OriginalRlpReadLengthCode
import InitECandidate.Runtime.OriginalRlpHeaderCode
import InitECandidate.Runtime.OriginalRlpUncheckedCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpFail_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_fail) :=
  memoryFrame_leaf _ (by simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)

/-- `rlp_read_length` keeps memory and globals in every outcome (including the `RlpErr` raise). -/
theorem rlpReadLength_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_read_length) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact memoryFrame_leaf _ (by decide)
    | apply memoryFrame_seq
    | apply memoryFrame_dec
    | apply memoryFrame_ite
    | apply memoryFrame_while
    | exact memoryFrame_discardCall _ _ _ _ _ originalRuntimeCode_rlpFail_lookup rlpFail_memoryFrame

/-- `rlp_item_header` keeps memory and globals in every outcome. -/
theorem rlpHeader_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_item_header) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact memoryFrame_leaf _ (by decide)
    | apply memoryFrame_seq
    | apply memoryFrame_dec
    | apply memoryFrame_ite
    | apply memoryFrame_while
    | exact memoryFrame_discardCall _ _ _ _ _ originalRuntimeCode_rlpFail_lookup rlpFail_memoryFrame
    | apply memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpReadLength_lookup rlpReadLength_memoryFrame

/-- `rlp_item_total_unchecked` keeps memory and globals in every outcome. -/
theorem rlpUnchecked_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact memoryFrame_leaf _ (by decide)
    | apply memoryFrame_seq
    | apply memoryFrame_dec
    | apply memoryFrame_ite
    | apply memoryFrame_while
    | exact memoryFrame_discardCall _ _ _ _ _ originalRuntimeCode_rlpFail_lookup rlpFail_memoryFrame
    | apply memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpReadLength_lookup rlpReadLength_memoryFrame

#print axioms rlpReadLength_memoryFrame
#print axioms rlpHeader_memoryFrame
#print axioms rlpUnchecked_memoryFrame
end InitECandidate.Runtime
