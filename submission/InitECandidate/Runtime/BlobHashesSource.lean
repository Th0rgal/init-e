import InitECandidate.Runtime.RlpSlicesTerminal
import InitECandidate.Runtime.RlpSlicesAdvances
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def blobHashesAfterSlices : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_decode_blob_hashes with
  | .decCall _ _ _ _ body => body
  | _ => .skip

def blobHashesInitialized : ProgHOL 64 :=
  match blobHashesAfterSlices with
  | .decCall _ _ _ _ body => body
  | _ => .skip

def blobHashesLoopAndReturn : ProgHOL 64 :=
  match blobHashesInitialized with
  | .dec _ _ _ body => body
  | _ => .skip

def blobHashesLoop : ProgHOL 64 :=
  match blobHashesLoopAndReturn with | .seq body _ => body | _ => .skip

def blobHashesStep : ProgHOL 64 :=
  match blobHashesLoop with | .while _ body => body | _ => .skip

theorem source_blobHashes_body : sourceFunctionBody Guest.guestFn_decode_blob_hashes =
    .decCall (ofString "lst") (.comb [.one,.one]) (ofString "rlp_list_to_slices")
      [.var .local (ofString "p"),.var .local (ofString "len")] blobHashesAfterSlices := by
  simp only [blobHashesAfterSlices,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_blobHashes_allocation : blobHashesAfterSlices =
    .decCall (ofString "buf") .one (ofString "alloc")
      [.panop .mul [.rfield 1 (.var .local (ofString "lst")),.const 32]] blobHashesInitialized := by
  simp only [blobHashesAfterSlices,blobHashesInitialized,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_blobHashes_initialized : blobHashesInitialized =
    .dec (ofString "i") .one (.const 0) blobHashesLoopAndReturn := by
  simp only [blobHashesAfterSlices,blobHashesInitialized,blobHashesLoopAndReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_blobHashes_loop_and_return : blobHashesLoopAndReturn =
    .seq blobHashesLoop (.return (.rstruct [.var .local (ofString "buf"),.rfield 1 (.var .local (ofString "lst"))])) := by
  simp only [blobHashesAfterSlices,blobHashesInitialized,blobHashesLoopAndReturn,blobHashesLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_blobHashes_loop : blobHashesLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) blobHashesStep := by
  simp only [blobHashesAfterSlices,blobHashesInitialized,blobHashesLoopAndReturn,blobHashesLoop,blobHashesStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_blobHashes_step : blobHashesStep =
    .decCall (ofString "h") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "lst")),.var .local (ofString "i"),.const 32]
      (.seq (.call (some (none,none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "i"),.const 32]],
         .var .local (ofString "h"),.const 32])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) := by
  simp only [blobHashesAfterSlices,blobHashesInitialized,blobHashesLoopAndReturn,blobHashesLoop,blobHashesStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- All original blob-decoder scopes terminate through return or an error,
including malformed arguments, failed allocation and exhausted clocks. -/
theorem evaluate_blobHashes_body_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_blob_hashes)).1 ≠ none := by
  rw [source_blobHashes_body]
  apply evaluate_decCall_terminal
  intro current
  rw [source_blobHashes_allocation]
  apply evaluate_decCall_terminal
  intro ready
  have terminal : ∀ current : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState current blobHashesLoopAndReturn).1 ≠ none := by
    intro current
    rw [source_blobHashes_loop_and_return]
    exact evaluate_seq_terminal current _ _ (fun output => evaluate_return_terminal output _)
  rw [source_blobHashes_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) ready) blobHashesLoopAndReturn with
  | mk result post =>
    have stopped := terminal (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) ready)
    rw [run] at stopped
    exact stopped

#print axioms evaluate_blobHashes_body_terminal
end InitECandidate.Runtime
