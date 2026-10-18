import InitECandidate.Runtime.FourWordStoreInputPrefix
import InitECandidate.Runtime.FourWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual transaction header store retains older slices below the transaction allocation. -/
theorem transaction_u256_header_outer_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx offset array count input inputLength : BitVec 64) (value : ValueHOL 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valueLocal : state.locals.lookup (ofString "v") = some value)
    (checked : shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one,.one]) = true)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + offset.toNat + 24 < 2^64) :
    RlpSliceInputPrefix
      (evaluateHOLFiniteState state (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v")))).2
      array input inputLength count.toNat := by
  obtain ⟨first,second,third,fourth,rfl⟩ := value_four_words_of_checked_shape value checked
  have addressNat : (tx + offset).toNat = tx.toNat + offset.toNat := by
    apply BitVec.toNat_add_of_lt
    omega
  apply fourWordStore_input_prefix state _ _ (tx + offset) first second third fourth array count input inputLength
  · simp [evalHOLExact,evalListHOLExact,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · simp [evalHOLExact,valueLocal]
  · exact valid
  · rw [addressNat]; omega
  · rw [addressNat]; exact fits

#print axioms transaction_u256_header_outer_prefix
end InitECandidate.Runtime
