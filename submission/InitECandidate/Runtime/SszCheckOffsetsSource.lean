import InitECandidate.Runtime.OriginalSszCheckOffsetsCode
import InitECandidate.Runtime.SszFixedListCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sszOffsetAddress : ExpHOL 64 :=
  .op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8]]

/-- Ordering check against the previous offset (only for i > 0). -/
def sszCheckPrevious : ProgHOL 64 :=
  .ite (.cmp .less (.const 0) (.var .local (ofString "i")))
    (.ite (.cmp .lower (.var .local (ofString "o")) (.load .one (.op .sub [sszOffsetAddress, .const 8])))
      (.call (some (none,none)) (ofString "ssz_fail") [.const 11]) .skip) .skip

/-- Range check of the current offset against the fixed part and input length. -/
def sszCheckRange : ProgHOL 64 :=
  .ite (.cmp .notEqual (.const 0) (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
      .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
    (.call (some (none,none)) (ofString "ssz_fail") [.const 10]) .skip

def sszCheckStep : ProgHOL 64 :=
  .dec (ofString "o") .one (.load .one sszOffsetAddress)
    (.seq sszCheckRange (.seq sszCheckPrevious
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))

def sszCheckLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) sszCheckStep

def sszCheckFinal : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed")))
      (.call (some (none,none)) (ofString "ssz_fail") [.const 12]) .skip)
    (.return (.const 0))

theorem source_sszCheckOffsets_body : sourceFunctionBody Guest.guestFn_ssz_check_offsets =
    .seq (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0)) (.return (.const 0)) .skip)
      (.dec (ofString "i") .one (.const 0) (.seq sszCheckLoop sszCheckFinal)) := by cbv

#print axioms source_sszCheckOffsets_body
end InitECandidate.Runtime
