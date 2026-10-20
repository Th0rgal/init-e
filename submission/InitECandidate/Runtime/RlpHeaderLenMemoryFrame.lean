import InitECandidate.Runtime.OriginalRlpWriterCode
import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.MptReadFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The body equation of the actual `rlp_be_len`: `n := 0; while v != 0 { v >>= 8; n += 1 }; return n`. -/
theorem source_rlpBeLen_body :
    sourceFunctionBody Guest.guestFn_rlp_be_len =
      .dec (ofString "n") .one (.const (0#64))
        (.seq (.while (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64)))
            (.seq (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const (8#64))))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const (1#64)]))))
          (.return (.var .local (ofString "n")))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpBeLen_body

/-- `rlp_be_len` writes no memory and touches no global: it only counts bytes of a local word.  This is
a `MemoryFrame`, so it can be used as a callee body frame for the header-length writers. -/
theorem rlpBeLen_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_be_len) := by
  rw [source_rlpBeLen_body]
  refine memoryFrame_dec _ _ _ (memoryFrame_seq (memoryFrame_while _ (memoryFrame_seq ?_ ?_)) ?_)
  · exact memoryFrame_leaf _ (by decide)
  · exact memoryFrame_leaf _ (by decide)
  · exact memoryFrame_leaf _ (by decide)

#print axioms rlpBeLen_memoryFrame

/-- The body equation of the actual `rlp_header_len`: the one-byte shortcut for `n <= 55`, otherwise the
`rlp_be_len` count plus its prefix byte. -/
theorem source_rlpHeaderLen_body :
    sourceFunctionBody Guest.guestFn_rlp_header_len =
      .seq (.ite (.cmp .notLower (.const (55#64)) (.var .local (ofString "n")))
          (.return (.const (1#64))) .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpHeaderLen_body

/-- `rlp_header_len` writes no memory: the shortcut returns immediately, the other branch only calls
`rlp_be_len` (which writes nothing) and returns a word. -/
theorem rlpHeaderLen_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_header_len) := by
  rw [source_rlpHeaderLen_body]
  refine memoryFrame_seq (memoryFrame_ite _
    (memoryFrame_leaf _ (by decide)) (memoryFrame_leaf _ (by decide)))
    (memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlp_be_len_lookup rlpBeLen_memoryFrame ?_)
  exact memoryFrame_leaf _ (by decide)

#print axioms rlpHeaderLen_memoryFrame

/-- The body equation of the actual `rlp_list_header_len`, a tail call into `rlp_header_len`. -/
theorem source_rlpListHeaderLen_body :
    sourceFunctionBody Guest.guestFn_rlp_list_header_len =
      .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpListHeaderLen_body

/-- `rlp_list_header_len` writes no memory: it is a tail call into `rlp_header_len`, whose body writes
nothing. -/
theorem rlpListHeaderLen_memoryFrame :
    MemoryFrame (sourceFunctionBody Guest.guestFn_rlp_list_header_len) := by
  rw [source_rlpListHeaderLen_body]
  exact memoryFrame_tailCall _ _ _ _ _ originalRuntimeCode_rlp_header_len_lookup rlpHeaderLen_memoryFrame

#print axioms rlpListHeaderLen_memoryFrame

end InitECandidate.Runtime
