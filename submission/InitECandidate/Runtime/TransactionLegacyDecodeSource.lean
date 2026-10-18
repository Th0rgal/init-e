import InitECandidate.Runtime.TransactionTypeFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionLegacyDecodeArguments : List (ExpHOL 64) :=
  [.var .local (ofString "p"),.var .local (ofString "len")]
def transactionLegacyPath : ProgHOL 64 :=
  match transactionTypeParseBranch with
  | .ite _ _ (.ite _ yes _) => yes
  | _ => .skip

theorem source_transaction_legacy_decode : transactionLegacyPath =
    .call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionLegacyDecodeArguments := by
  simp only [transactionLegacyDecodeArguments,transactionLegacyPath,transactionTypeParseBranch,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_legacy_decode_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length))) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) transactionLegacyDecodeArguments =
      some [.val (.word pointer),.val (.word length)] := by
  simp [transactionLegacyDecodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]

#print axioms source_transaction_legacy_decode
#print axioms transaction_legacy_decode_arguments
end InitECandidate.Runtime
