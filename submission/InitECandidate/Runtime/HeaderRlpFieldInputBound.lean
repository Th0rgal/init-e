import InitECandidate.Runtime.HeaderRlpFieldBound
import InitECandidate.Runtime.RlpSliceInputSpan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def headerRlpFieldCost (limit : Nat) : Nat := limit * ((2 * limit + 1) * 15 + 19) + 92633

/-- Header-field parsing reads the concrete pointer and length of its actual slice-array entry. -/
theorem eval_header_rlp_field_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength : BitVec 64)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) headerRlpFieldArguments =
      some [.val (.word pointer),.val (.word length)] := by
  have sourceDomain := entry.readable.pointerDomain
  have sizeDomain := entry.readable.lengthDomain
  have sourceCell := entry.readable.pointerCell
  have sizeCell := entry.readable.lengthCell
  rw [evalListHOLFinite_eq_toExact]
  simp [headerRlpFieldArguments,evalListHOLExact,evalHOLExact,atArray,atIndex,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    sourceDomain,sizeDomain,sourceCell,sizeCell]
  have sizeDomainRight : s.memaddrs (array + (index * (16#64) + (8#64))) := by
    simpa only [BitVec.add_assoc] using sizeDomain
  simp [sourceDomain,sizeDomainRight,sourceCell,sizeCell,← BitVec.add_assoc]
  rw [if_pos sizeDomainRight]

/-- The actual bounded slice contract supplies parser readability, input fit
and a uniform input-quadratic bound for the original raw/bytes/uint helpers. -/
theorem runBounded_header_rlp_field_input {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderRlpField)
    (array index pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit ≤ s.clock) :
    RunBounded s (sourceFunctionBody (headerRlpFieldDeclaration field)) (headerRlpFieldCost inputLimit) := by
  have lengthBound : length.toNat ≤ inputLimit := (entry.length_bound s array index pointer length input inputLength).trans inputBound
  have monotone : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ headerRlpFieldCost inputLimit := by
    have product := Nat.mul_le_mul lengthBound (by omega : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLimit + 1) * 15 + 19)
    unfold headerRlpFieldCost
    omega
  exact (runBounded_header_rlp_field s field pointer length scratch frame ceiling inputLimit
    (eval_header_rlp_field_arguments s array index pointer length input inputLength atArray atIndex entry)
    entry.noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (monotone.trans budget)).weaken monotone

#print axioms eval_header_rlp_field_arguments
#print axioms runBounded_header_rlp_field_input
end InitECandidate.Runtime
