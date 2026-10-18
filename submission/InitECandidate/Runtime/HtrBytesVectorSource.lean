import InitECandidate.Runtime.HtrBytesVectorLongBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrBytesVectorShort : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "out"),.const 32])
    (.seq (.call (some (none,none)) (ofString "memcpy")
      [.var .local (ofString "out"),.var .local (ofString "p"),.var .local (ofString "n")]) (.return (.const 0)))

def htrBytesVectorCheck : ProgHOL 64 :=
  .ite (.cmp .notLower (.const 32) (.var .local (ofString "n"))) htrBytesVectorShort .skip

theorem source_htrBytesVector_body : sourceFunctionBody Guest.guestFn_htr_bytes_vector =
    .seq htrBytesVectorCheck (htrBytesVectorLongAt 0) := by
  rw [sourceFunctionBody_eq_structural]; rfl

#print axioms source_htrBytesVector_body
end InitECandidate.Runtime
