import InitECandidate.Runtime.AuthorizationsTailSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_decode_access_list
  | n + 1 => authorizationNext (accessAt n)
def accessStep := accessAt 5
def accessItemCheck := accessAt 6
def accessInnerSlices := accessAt 7
def accessEntryCheck := accessAt 8
def accessAddress := accessAt 9
def accessSlotItem := accessAt 10
def accessSlotSlices := accessAt 11
def accessKeysAllocation := accessAt 12
def accessKeysInitialization := accessAt 13
def accessKeysLoopAndRecord := accessAt 14
def accessKeysLoop := accessAt 15
def accessKeysStep := accessAt 16
def accessKeysCopy := accessAt 17
def accessRecordScope : ProgHOL 64 :=
  match accessKeysLoopAndRecord with | .seq _ tail => tail | _ => .skip

theorem source_access_keys_step : accessKeysStep =
    .decCall (ofString "k") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "slots")),.var .local (ofString "j"),.const 32] accessKeysCopy := by
  simp only [accessKeysStep,accessKeysCopy,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_access_keys_copy : accessKeysCopy =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.const 32]],
       .var .local (ofString "k"),.const 32])
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) := by
  simp only [accessKeysCopy,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_access_keys_loop : accessKeysLoop =
    .while (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "slots")))) accessKeysStep := by
  simp only [accessKeysLoop,accessKeysStep,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_access_keys_loop_and_record : accessKeysLoopAndRecord = .seq accessKeysLoop accessRecordScope := by
  simp only [accessKeysLoopAndRecord,accessKeysLoop,accessRecordScope,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_access_keys_step
#print axioms source_access_keys_loop_and_record
end InitECandidate.Runtime
