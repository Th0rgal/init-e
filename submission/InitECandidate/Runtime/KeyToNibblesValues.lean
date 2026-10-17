import InitECandidate.Runtime.TrieNibbleStore
import InitECandidate.Runtime.KeyToNibblesSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The high-nibble source shift is bounded because its operand was a byte. -/
theorem keyNibble_high_small (byte : UInt8) :
    ((BitVec.ofNat 64 byte.toNat) >>> (4 : Nat)).toNat < 16 := by
  have bound := byte.toBitVec.isLt
  change byte.toNat < 256 at bound
  rw [BitVec.toNat_ushiftRight]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow]
  change byte.toNat % 18446744073709551616 / 16 < 16
  omega

/-- Masking bounds the low nibble even without an operand range premise. -/
theorem keyNibble_low_small (word : BitVec 64) : (word &&& 15).toNat < 16 := by
  rw [BitVec.toNat_and]
  have bound := Nat.and_le_right (n := word.toNat) (m := (15 : BitVec 64).toNat)
  change word.toNat &&& 15 < 16
  change word.toNat &&& 15 ≤ 15 at bound
  omega

/-- Both expressions in the original conversion evaluate to bounded words. -/
theorem eval_keyNibble_values {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (byte : UInt8)
    (localByte : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat)))) :
    (@evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.shift .lsr (.var .local name) (.const 4)) =
        some (.val (.word ((BitVec.ofNat 64 byte.toNat) >>> (4 : Nat))))) ∧
    (@evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.var .local name,.const 15]) =
        some (.val (.word ((BitVec.ofNat 64 byte.toNat) &&& 15)))) := by
  constructor <;>
    simp [evalHOLExact,evalListHOLExact,localByte,wordShiftHOL,wordOpHOL,wordOp,valueIsWord,valueWord]
  change (BitVec.ofNat 64 byte.toNat) &&& ((15 : BitVec 64) &&& 18446744073709551615) = _
  bv_decide

def keyNibbleOutputAddress (offset : Nat) : ExpHOL 64 :=
  .op .add ([.var .local (ofString "out"),
    .panop .mul [.const 2,.var .local (ofString "i")]] ++
    if offset = 0 then [] else [.const (BitVec.ofNat 64 offset)])

/-- The checked expressions are exactly the two writes in the source tail. -/
theorem source_keyNibble_tail_step : keyToNibblesTailStep =
    .dec (ofString "b") .one
      (.loadByte (.op .add [.var .local (ofString "key"),.var .local (ofString "i")]))
      (.seq (.storeByte (keyNibbleOutputAddress 0)
        (.shift .lsr (.var .local (ofString "b")) (.const 4)))
        (.seq (.storeByte (keyNibbleOutputAddress 1)
          (.op .and [.var .local (ofString "b"),.const 15]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 1])))) := by
  simp only [keyToNibblesTailStep,keyToNibblesTailLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_keyNibble_tail_step
#print axioms keyNibble_high_small
#print axioms keyNibble_low_small
#print axioms eval_keyNibble_values
end InitECandidate.Runtime
