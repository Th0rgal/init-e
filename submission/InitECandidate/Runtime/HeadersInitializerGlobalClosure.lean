import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.GlobalKeep
import InitECandidate.Runtime.OriginalValidateHeadersCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-- Actual header-validation call closure for protected world globals. -/
def headersInitializerGlobalGood (name : MlS) : Bool :=
 [ofString "_rlp_validate_items_body",ofString "alloc",ofString "bswap64",ofString "decode_header",ofString "hdr_bytes_field",ofString "hdr_raw_field",ofString "hdr_u256_field",ofString "hdr_uint_field",ofString "hdr_word_field",ofString "keccak256",ofString "keccak_absorb_block",ofString "keccak_f1600",ofString "memcpy",ofString "memeq",ofString "memzero",ofString "rlp_decode_fully",ofString "rlp_fail",ofString "rlp_item",ofString "rlp_item_header",ofString "rlp_item_total",ofString "rlp_item_total_unchecked",ofString "rlp_list_count",ofString "rlp_list_to_slices",ofString "rlp_read_length",ofString "rlp_validate_items",ofString "scratch_alloc",ofString "scratch_mark",ofString "scratch_release",ofString "trap_with",ofString "u256_from_be",ofString "validate_headers"].contains name
/-- Initialized globals required by the subsequent world/trie initializer. -/
def headersInitializerGlobals : List MlS :=
 [ofString "ws",ofString "bs",ofString "empty_trie_root",ofString "mpt_hash_scratch"]

theorem headers_initializer_global_check : (functionsHOL sourceDeclarations).all
 (fun entry => !headersInitializerGlobalGood entry.1 ||
  headersInitializerGlobals.all (fun watched => keepsG watched headersInitializerGlobalGood entry.2.2.1))=true := by
 decide_cbv

theorem headers_initializer_global_installed {function watched : MlS}
 {parameters : List (MlS × ShapeHOL)} {body : ProgHOL 64} {shape : ShapeHOL}
 (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
 (good : headersInitializerGlobalGood function=true) (member : watched∈headersInitializerGlobals) :
 keepsG watched headersInitializerGlobalGood body=true := by
 have checked := List.all_eq_true.mp headers_initializer_global_check _ (originalRuntimeCode_mem installed)
 have all : headersInitializerGlobals.all (fun key => keepsG key headersInitializerGlobalGood body)=true := by
  simpa [good] using checked
 exact List.all_eq_true.mp all watched member

theorem evaluate_headers_initializer_global {F : Type} (s : PanSemStateFiniteExact 64 F)
 (program : ProgHOL 64) (watched : MlS) (member : watched∈headersInitializerGlobals)
 (supported : keepsG watched headersInitializerGlobalGood program=true) (code : s.code=originalRuntimeCode) :
 (evaluateHOLFiniteState s program).2.globals.lookup watched=s.globals.lookup watched := by
 apply evaluate_keepsG watched headersInitializerGlobalGood
 · intro function good values body callee shape lookup
   obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
   exact headers_initializer_global_installed installed good member
 · exact supported
 · exact code

#print axioms headers_initializer_global_check
#print axioms headers_initializer_global_installed
#print axioms evaluate_headers_initializer_global
end InitECandidate.Runtime
