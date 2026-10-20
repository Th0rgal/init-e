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
def nodedbInitializerGlobalGood (name : MlS) : Bool :=
 [ofString "alloc",ofString "htab_find_slot",ofString "htab_grow",ofString "htab_hash",ofString "htab_insert_raw",ofString "htab_new",ofString "htab_set",ofString "keccak256",ofString "keccak_absorb_block",ofString "keccak_f1600",ofString "memcpy",ofString "memeq",ofString "memzero",ofString "nodedb_build",ofString "trap_with"].contains name
/-- Initialized globals required by the subsequent world/trie initializer. -/
def nodedbInitializerGlobals : List MlS :=
 [ofString "ws",ofString "bs",ofString "scratch_ptr",ofString "frame_mem_ptr",ofString "empty_trie_root"]

theorem nodedb_initializer_global_check : (functionsHOL sourceDeclarations).all
 (fun entry => !nodedbInitializerGlobalGood entry.1 ||
  nodedbInitializerGlobals.all (fun watched => keepsG watched nodedbInitializerGlobalGood entry.2.2.1))=true := by
 decide_cbv

theorem nodedb_initializer_global_installed {function watched : MlS}
 {parameters : List (MlS × ShapeHOL)} {body : ProgHOL 64} {shape : ShapeHOL}
 (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
 (good : nodedbInitializerGlobalGood function=true) (member : watched∈nodedbInitializerGlobals) :
 keepsG watched nodedbInitializerGlobalGood body=true := by
 have checked := List.all_eq_true.mp nodedb_initializer_global_check _ (originalRuntimeCode_mem installed)
 have all : nodedbInitializerGlobals.all (fun key => keepsG key nodedbInitializerGlobalGood body)=true := by
  simpa [good] using checked
 exact List.all_eq_true.mp all watched member

theorem evaluate_nodedb_initializer_global {F : Type} (s : PanSemStateFiniteExact 64 F)
 (program : ProgHOL 64) (watched : MlS) (member : watched∈nodedbInitializerGlobals)
 (supported : keepsG watched nodedbInitializerGlobalGood program=true) (code : s.code=originalRuntimeCode) :
 (evaluateHOLFiniteState s program).2.globals.lookup watched=s.globals.lookup watched := by
 apply evaluate_keepsG watched nodedbInitializerGlobalGood
 · intro function good values body callee shape lookup
   obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
   exact nodedb_initializer_global_installed installed good member
 · exact supported
 · exact code

#print axioms nodedb_initializer_global_check
#print axioms nodedb_initializer_global_installed
#print axioms evaluate_nodedb_initializer_global
end InitECandidate.Runtime
