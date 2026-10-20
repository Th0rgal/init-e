import InitECandidate.Runtime.DecodeWitnessNodeLoopSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 def decodeWitnessMptAfterLocals : ProgHOL 64 := stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt)
 def decodeWitnessMptHandler : ProgHOL 64 :=
  match decodeWitnessMptAfterLocals with
  | .seq (.call (some (_,some (_,_,handler))) _ _) _ => handler | _ => .skip
 def decodeWitnessAfterMark : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__decode_witness_node with | .decCall _ _ _ _ tail => tail | _ => .skip
 def decodeWitnessAfterLocals : ProgHOL 64 := stateInitSpineDrop 2 decodeWitnessAfterMark
 def decodeWitnessRlpHandler : ProgHOL 64 :=
  match decodeWitnessAfterLocals with
  | .seq (.call (some (_,some (_,_,handler))) _ _) _ => handler | _ => .skip
 def decodeWitnessCleanup : ProgHOL 64 :=
  match decodeWitnessAfterLocals with | .seq _ tail => tail | _ => .skip
 theorem source_decode_witness_mpt_body : sourceFunctionBody Guest.guestFn__decode_witness_node_mpt =
    .dec (ofString "e") .one (.const 0) (.dec (ofString "nd") .one (.const 0) decodeWitnessMptAfterLocals) := by
  simp only [decodeWitnessMptAfterLocals,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_mpt_after_locals : decodeWitnessMptAfterLocals =
    .seq (.call (some (some (.local,ofString "nd"),some (ofString "MptErr",ofString "e",decodeWitnessMptHandler)))
      (ofString "_decode_witness_node_body") [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n")])
      (.return (.var .local (ofString "nd"))) := by
  simp only [decodeWitnessMptHandler,decodeWitnessMptAfterLocals,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_mpt_handler : decodeWitnessMptHandler =
    .seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")])
      (.raise (ofString "MptErr") (.var .local (ofString "e"))) := by
  simp only [decodeWitnessMptHandler,decodeWitnessMptAfterLocals,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_body : sourceFunctionBody Guest.guestFn__decode_witness_node =
    .decCall (ofString "mark") .one (ofString "scratch_mark") [] decodeWitnessAfterMark := by
  simp only [decodeWitnessAfterMark,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_after_mark : decodeWitnessAfterMark =
    .dec (ofString "e") .one (.const 0) (.dec (ofString "nd") .one (.const 0) decodeWitnessAfterLocals) := by
  simp only [decodeWitnessAfterLocals,decodeWitnessAfterMark,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_after_locals : decodeWitnessAfterLocals =
    .seq (.call (some (some (.local,ofString "nd"),some (ofString "RlpErr",ofString "e",decodeWitnessRlpHandler)))
      (ofString "_decode_witness_node_mpt") [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n"),.var .local (ofString "mark")])
      decodeWitnessCleanup := by
  simp only [decodeWitnessRlpHandler,decodeWitnessCleanup,decodeWitnessAfterLocals,decodeWitnessAfterMark,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_rlp_handler : decodeWitnessRlpHandler =
    .seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")])
      (.raise (ofString "RlpErr") (.var .local (ofString "e"))) := by
  simp only [decodeWitnessRlpHandler,decodeWitnessAfterLocals,decodeWitnessAfterMark,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
 theorem source_decode_witness_cleanup : decodeWitnessCleanup =
    .seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")])
      (.return (.var .local (ofString "nd"))) := by
  simp only [decodeWitnessCleanup,decodeWitnessAfterLocals,decodeWitnessAfterMark,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq];rfl
#print axioms source_decode_witness_mpt_body
#print axioms source_decode_witness_mpt_after_locals
#print axioms source_decode_witness_mpt_handler
#print axioms source_decode_witness_body
#print axioms source_decode_witness_after_mark
#print axioms source_decode_witness_after_locals
#print axioms source_decode_witness_rlp_handler
#print axioms source_decode_witness_cleanup
end InitECandidate.Runtime
