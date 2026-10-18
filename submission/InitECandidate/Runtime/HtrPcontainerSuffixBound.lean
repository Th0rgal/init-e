import InitECandidate.Runtime.HtrPcontainerSource
import InitECandidate.Runtime.Sha256PairBound
import InitECandidate.Runtime.VariableCountedDeclaration
import InitECandidate.Runtime.VmFn_heap_release
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrPcontainer_mask_counted : CountedBody (ofString "i") 1 htrPcontainerMaskBody (0 + 0) := by
  rw [source_htrPcontainer_mask_body]
  exact CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide) CountedBody.incr

theorem htrPcontainer_finish_bounded : ProgBounded (htrPcontainerAt 7) (136 + (1 + 0)) := by
  rw [source_htrPcontainer_finish]
  exact ProgBounded.seq (ProgBounded.call sha256Pair_funBounded _ _)
    (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))

def htrPcontainerSuffixCost : Nat := 16 + ((2 ^ 64 - 1) * 1 + 137)

/-- The actual bitmask stores, final SHA call and heap release have a uniform
finite bound, including malformed local values and memory errors. -/
theorem htrPcontainer_suffix_bounded : ProgBounded (htrPcontainerAt 3) htrPcontainerSuffixCost := by
  rw [source_htrPcontainer_act]
  apply ProgBounded.dec
  rw [source_htrPcontainer_zero]
  apply ProgBounded.seq (memzero_const_progBounded _ 32 (by decide))
  rw [source_htrPcontainer_mask]
  exact ProgBounded.variableCountedDec (ofString "i") (ofString "n") .less (Or.inl rfl)
    htrPcontainer_mask_counted (by decide) htrPcontainer_finish_bounded

#print axioms htrPcontainer_mask_counted
#print axioms htrPcontainer_finish_bounded
#print axioms htrPcontainer_suffix_bounded
end InitECandidate.Runtime
