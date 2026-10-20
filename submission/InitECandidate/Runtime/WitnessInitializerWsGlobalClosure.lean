import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.GlobalKeep
import InitECandidate.Runtime.OriginalNodedbBuildCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-- Actual database-build call closure; only alloc writes a global frontier. -/
def witnessInitializerWsGood (name : MlS) : Bool :=
 [ofString "_decode_step",ofString "_decode_witness_node",ofString "_decode_witness_node_body",ofString "_decode_witness_node_mpt",ofString "_resolve_step",ofString "_rlp_validate_items_body",ofString "alloc",ofString "compact_to_nibbles",ofString "decode_witness_to_mpt",ofString "htab_find_slot",ofString "htab_get",ofString "htab_hash",ofString "key_to_nibbles",ofString "memcpy",ofString "memeq",ofString "memzero",ofString "mpt_fail",ofString "node_new_branch",ofString "node_new_ext",ofString "node_new_hashed",ofString "node_new_leaf",ofString "nodedb_lookup",ofString "rlp_decode_fully",ofString "rlp_fail",ofString "rlp_item",ofString "rlp_item_header",ofString "rlp_item_total",ofString "rlp_item_total_unchecked",ofString "rlp_list_count",ofString "rlp_list_to_slices",ofString "rlp_read_length",ofString "rlp_validate_items",ofString "scratch_alloc",ofString "scratch_mark",ofString "scratch_release",ofString "trap_with"].contains name
/-- Initialized globals required by the subsequent world/trie initializer. -/
def witnessInitializerWatchedGlobals : List MlS :=
 [ofString "ws"]

theorem witness_initializer_ws_global_check : (functionsHOL sourceDeclarations).all
 (fun entry => !witnessInitializerWsGood entry.1 ||
  witnessInitializerWatchedGlobals.all (fun watched => keepsG watched witnessInitializerWsGood entry.2.2.1))=true := by
 decide_cbv

theorem witness_initializer_ws_global_installed {function watched : MlS}
 {parameters : List (MlS × ShapeHOL)} {body : ProgHOL 64} {shape : ShapeHOL}
 (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
 (good : witnessInitializerWsGood function=true) (member : watched∈witnessInitializerWatchedGlobals) :
 keepsG watched witnessInitializerWsGood body=true := by
 have checked := List.all_eq_true.mp witness_initializer_ws_global_check _ (originalRuntimeCode_mem installed)
 have all : witnessInitializerWatchedGlobals.all (fun key => keepsG key witnessInitializerWsGood body)=true := by
  simpa [good] using checked
 exact List.all_eq_true.mp all watched member

theorem evaluate_witness_initializer_ws_global {F : Type} (s : PanSemStateFiniteExact 64 F)
 (program : ProgHOL 64) (watched : MlS) (member : watched∈witnessInitializerWatchedGlobals)
 (supported : keepsG watched witnessInitializerWsGood program=true) (code : s.code=originalRuntimeCode) :
 (evaluateHOLFiniteState s program).2.globals.lookup watched=s.globals.lookup watched := by
 apply evaluate_keepsG watched witnessInitializerWsGood
 · intro function good values body callee shape lookup
   obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
   exact witness_initializer_ws_global_installed installed good member
 · exact supported
 · exact code

#print axioms witness_initializer_ws_global_check
#print axioms witness_initializer_ws_global_installed
#print axioms evaluate_witness_initializer_ws_global
end InitECandidate.Runtime
