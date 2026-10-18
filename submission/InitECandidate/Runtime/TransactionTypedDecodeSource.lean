import InitECandidate.Runtime.TransactionTypeAssignSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionTypedDecodeArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.const 1],.op .sub [.var .local (ofString "len"),.const 1]]

theorem source_transaction_typed_decode : transactionTypedPath =
    .seq (.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionTypedDecodeArguments)
      (.seq transactionTypeAssign transactionTypeFields) := by
  simp only [transactionTypedDecodeArguments,transactionTypeAssign,transactionTypeFields,transactionTypeFieldCase,
    transactionTypedPath,transactionTypeParseBranch,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_typed_decode_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length))) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) transactionTypedDecodeArguments =
      some [.val (.word (pointer + 1)),.val (.word (length - 1))] := by
  simp [transactionTypedDecodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord]

/-- Removing the transaction type byte preserves the original input endpoint. -/
theorem transaction_typed_decode_range (pointer length : BitVec 64)
    (positive : 0 < length.toNat) (noWrap : pointer.toNat + length.toNat < 2^64) :
    (pointer + 1).toNat = pointer.toNat + 1 ∧
    (length - 1).toNat = length.toNat - 1 ∧
    (pointer + 1).toNat + (length - 1).toNat = pointer.toNat + length.toNat ∧
    (length - 1).toNat ≤ length.toNat := by
  have add : (pointer + 1).toNat = pointer.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change pointer.toNat + 1 < 2^64; omega)]
    rfl
  have sub : (length - 1).toNat = length.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ length.toNat; omega)]
    rfl
  exact ⟨add,sub,by omega,by omega⟩

#print axioms source_transaction_typed_decode
#print axioms transaction_typed_decode_arguments
#print axioms transaction_typed_decode_range
end InitECandidate.Runtime
