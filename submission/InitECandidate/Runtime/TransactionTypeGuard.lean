import InitECandidate.Runtime.TransactionTypedDecodeSource
import InitECandidate.Runtime.TransactionLegacyDecodeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionByteRange (low high : BitVec 64) : ExpHOL 64 :=
  .op .and [
    .cmp .notEqual (.const 0) (.cmp .notLower (.var .local (ofString "b0")) (.const low)),
    .cmp .notEqual (.const 0) (.cmp .notLower (.const high) (.var .local (ofString "b0")))]

theorem source_transaction_type_branch : transactionTypeParseBranch =
    .ite (transactionByteRange 1 4) transactionTypedPath
      (.ite (transactionByteRange 192 254) transactionLegacyPath (.raise (ofString "TxErr") (.const 2))) := by
  simp only [transactionByteRange,transactionTypeParseBranch,transactionTypedPath,transactionLegacyPath,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_transaction_type_parse : transactionAt 9 = .seq transactionTypeParseBranch (transactionAt 10) := by
  simp only [transactionTypeParseBranch,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_transaction_byte_range {F : Type} (state : PanSemStateFiniteExact 64 F)
    (byte low high : BitVec 64)
    (binding : state.locals.lookup (ofString "b0") = some (.val (.word byte))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (transactionByteRange low high) =
      some (.val (.word (if ¬ byte < low ∧ ¬ high < byte then (1 : BitVec 64) else 0))) := by
  by_cases below : byte < low <;> by_cases above : high < byte <;>
    simp [transactionByteRange,evalHOLExact,evalListHOLExact,binding,Compiler.Encoders.Asm.wordCmpHOL,
      wordOpHOL,wordOp,valueIsWord,valueWord,below,above] <;> decide

theorem transaction_typed_guard_supported (byte : BitVec 64)
    (lower : ¬ byte < 1#64) (upper : ¬ 4#64 < byte) :
    byte = 0 ∨ byte = 1 ∨ byte = 2 ∨ byte = 3 ∨ byte = 4 := by
  have low : 1 ≤ byte.toNat := by
    have h : ¬ byte.toNat < (1 : BitVec 64).toNat := fun h => lower (BitVec.lt_def.mpr h)
    change ¬ byte.toNat < 1 at h
    omega
  have high : byte.toNat ≤ 4 := by
    have h : ¬ (4 : BitVec 64).toNat < byte.toNat := fun h => upper (BitVec.lt_def.mpr h)
    change ¬ 4 < byte.toNat at h
    omega
  have cases : byte.toNat = 1 ∨ byte.toNat = 2 ∨ byte.toNat = 3 ∨ byte.toNat = 4 := by omega
  rcases cases with one | two | three | four
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq one))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq two)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq three))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq four))))

#print axioms source_transaction_type_branch
#print axioms source_transaction_type_parse
#print axioms evaluate_transaction_byte_range
#print axioms transaction_typed_guard_supported
end InitECandidate.Runtime
