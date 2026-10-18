import InitECandidate.Runtime.OriginalSszSplitVarListCode
import InitECandidate.Runtime.SszFailFreeFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sszLocal (name : String) : ExpHOL 64 := .var .local (ofString name)

/-- Little-endian 32-bit read of the first offset at p. -/
def sszSplitFirst : ExpHOL 64 :=
  .op .or [.loadByte (sszLocal "p"),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 3])) (.const 24)]

def sszSplitIndex4 : ExpHOL 64 := .panop .mul [sszLocal "i", .const 4]

/-- Little-endian 32-bit read of offset i at p + 4i. -/
def sszSplitOffsetAt : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [sszLocal "p", sszSplitIndex4]),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", sszSplitIndex4, .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", sszSplitIndex4, .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", sszSplitIndex4, .const 3])) (.const 24)]

def sszSplitCheck : ProgHOL 64 :=
  .ite (.cmp .notEqual (.const 0) (.op .or [.cmp .lower (sszLocal "o") (sszLocal "first"),
      .cmp .lower (sszLocal "len") (sszLocal "o"), .cmp .lower (sszLocal "o") (sszLocal "prev")]))
    (.call (some (none,none)) (ofString "ssz_fail") [.const 23]) .skip

def sszSplitStorePrev : ProgHOL 64 :=
  .ite (.cmp .less (.const 0) (sszLocal "i"))
    (.store (.op .add [sszLocal "arr", .panop .mul [.op .sub [sszLocal "i", .const 1], .const 16], .const 8])
      (.op .sub [sszLocal "o", sszLocal "prev"])) .skip

def sszSplitStoreCur : ProgHOL 64 :=
  .store (.op .add [sszLocal "arr", .panop .mul [sszLocal "i", .const 16]]) (.op .add [sszLocal "p", sszLocal "o"])

def sszSplitStep : ProgHOL 64 :=
  .dec (ofString "o") .one sszSplitOffsetAt
    (.seq sszSplitCheck (.seq sszSplitStorePrev (.seq sszSplitStoreCur
      (.seq (.assign .local (ofString "prev") (sszLocal "o"))
        (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1]))))))

def sszSplitLoop : ProgHOL 64 := .while (.cmp .less (sszLocal "i") (sszLocal "count")) sszSplitStep

def sszSplitTail : ProgHOL 64 :=
  .seq (.store (.op .add [sszLocal "arr", .panop .mul [.op .sub [sszLocal "count", .const 1], .const 16], .const 8])
      (.op .sub [sszLocal "len", sszLocal "prev"]))
    (.return (.rstruct [sszLocal "arr", sszLocal "count"]))

def sszSplitAfterAlloc : ProgHOL 64 :=
  .dec (ofString "i") .one (.const 0) (.dec (ofString "prev") .one (sszLocal "first") (.seq sszSplitLoop sszSplitTail))

def sszSplitFirstCheck : ProgHOL 64 :=
  .ite (.cmp .notEqual (.const 0) (.op .or [.cmp .equal (sszLocal "first") (.const 0),
      .cmp .notEqual (.op .and [sszLocal "first", .const 3]) (.const 0), .cmp .lower (sszLocal "len") (sszLocal "first")]))
    (.call (some (none,none)) (ofString "ssz_fail") [.const 21]) .skip

def sszSplitCountCheck : ProgHOL 64 :=
  .ite (.cmp .lower (sszLocal "lim") (sszLocal "count")) (.call (some (none,none)) (ofString "ssz_fail") [.const 22]) .skip

def sszSplitAlloc : ProgHOL 64 :=
  .decCall (ofString "arr") .one (ofString "alloc") [.panop .mul [sszLocal "count", .const 16]] sszSplitAfterAlloc

def sszSplitAfterFirst : ProgHOL 64 :=
  .seq sszSplitFirstCheck (.dec (ofString "count") .one (.shift .lsr (sszLocal "first") (.const 2))
    (.seq sszSplitCountCheck sszSplitAlloc))

theorem source_sszSplitVarList_body : sourceFunctionBody Guest.guestFn_ssz_split_var_list =
    .seq (.ite (.cmp .equal (sszLocal "len") (.const 0)) (.return (.rstruct [.const 0, .const 0])) .skip)
      (.seq (.ite (.cmp .lower (sszLocal "len") (.const 4)) (.call (some (none,none)) (ofString "ssz_fail") [.const 20]) .skip)
        (.dec (ofString "first") .one sszSplitFirst sszSplitAfterFirst)) := by cbv

#print axioms source_sszSplitVarList_body
end InitECandidate.Runtime
