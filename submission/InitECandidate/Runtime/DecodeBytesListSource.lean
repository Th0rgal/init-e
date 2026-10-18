import InitECandidate.Runtime.OriginalDecodeBytesListCode
import InitECandidate.Runtime.SszSplitVarListSlicesBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def bytesListLenAddress : ExpHOL 64 :=
  .op .add [.rfield 0 (sszLocal "r"), .panop .mul [sszLocal "i", .const 16], .const 8]

def bytesListStep : ProgHOL 64 :=
  .seq (.ite (.cmp .lower (sszLocal "maxb") (.load .one bytesListLenAddress))
      (.call (some (none,none)) (ofString "ssz_fail") [.const 70]) .skip)
    (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1]))

def bytesListLoop : ProgHOL 64 := .while (.cmp .less (sszLocal "i") (.rfield 1 (sszLocal "r"))) bytesListStep

def bytesListAfterSplit : ProgHOL 64 :=
  .dec (ofString "i") .one (.const 0) (.seq bytesListLoop (.return (sszLocal "r")))

theorem source_decodeBytesList_body : sourceFunctionBody Guest.guestFn_decode_bytes_list =
    .decCall (ofString "r") (.comb [.one,.one]) (ofString "ssz_split_var_list")
      [sszLocal "p", sszLocal "len", sszLocal "lim"] bytesListAfterSplit := by cbv

#print axioms source_decodeBytesList_body
end InitECandidate.Runtime
