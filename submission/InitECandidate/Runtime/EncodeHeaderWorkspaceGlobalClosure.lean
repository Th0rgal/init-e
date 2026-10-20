import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.GlobalKeep
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-- Actual transitive original encode_header source call closure. -/
def encodeHeaderWorkspaceGood (name : MlS) : Bool :=
 [ofString "alloc", ofString "bit_length64", ofString "encode_header", ofString "heap_mark", ofString "heap_release", ofString "memcpy", ofString "rlp_be_len", ofString "rlp_encode_bytes", ofString "rlp_encode_list_header", ofString "rlp_encode_word", ofString "rlp_header_len", ofString "rlp_list_header_len", ofString "rlp_put_be", ofString "rlp_put_u256", ofString "rlp_write_header", ofString "trap_with", ofString "u256_bit_length", ofString "u256_byte_length", ofString "u256_limb", ofString "u256_to_be_min"].contains name
def encodeHeaderWorkspaceGlobals : List MlS := [ofString "keccak_st",ofString "keccak_pad"]
theorem encode_header_workspace_globals_check : (functionsHOL sourceDeclarations).all
 (fun entry=>!encodeHeaderWorkspaceGood entry.1 || encodeHeaderWorkspaceGlobals.all
  (fun watched=>keepsG watched encodeHeaderWorkspaceGood entry.2.2.1))=true := by decide_cbv

theorem encode_header_workspace_global_installed {function watched : MlS}
 {parameters : List (MlS×ShapeHOL)} {body : ProgHOL 64} {shape : ShapeHOL}
 (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
 (good : encodeHeaderWorkspaceGood function=true) (member : watched∈encodeHeaderWorkspaceGlobals) :
 keepsG watched encodeHeaderWorkspaceGood body=true := by
 have checked:=List.all_eq_true.mp encode_header_workspace_globals_check _ (originalRuntimeCode_mem installed)
 have all : encodeHeaderWorkspaceGlobals.all (fun key=>keepsG key encodeHeaderWorkspaceGood body)=true := by
  simpa [good] using checked
 exact List.all_eq_true.mp all watched member

theorem evaluate_encode_header_workspace_global {F : Type} (s : PanSemStateFiniteExact 64 F)
 (program : ProgHOL 64) (watched : MlS) (member : watched∈encodeHeaderWorkspaceGlobals)
 (supported : keepsG watched encodeHeaderWorkspaceGood program=true) (code : s.code=originalRuntimeCode) :
 (evaluateHOLFiniteState s program).2.globals.lookup watched=s.globals.lookup watched := by
 apply evaluate_keepsG watched encodeHeaderWorkspaceGood
 · intro function good values body callee shape lookup
   obtain ⟨parameters,returnShape,installed⟩:=lookupCode_installed lookup
   exact encode_header_workspace_global_installed installed good member
 · exact supported
 · exact code
#print axioms encode_header_workspace_globals_check
#print axioms encode_header_workspace_global_installed
#print axioms evaluate_encode_header_workspace_global
end InitECandidate.Runtime
