import InitECandidate.Runtime.DecodeHeaderLastBytesReach
import InitECandidate.Runtime.HeaderExpressionStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def decodeHeaderCurrentCondition : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "is_current")) (.const 0)

def decodeHeaderCurrentSuffix : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "f"),none)) (ofString "hdr_bytes_field")
    [.var .local (ofString "arr"),.const 21,.const 32])
    (.seq (headerWordStore (ofString "f") 232)
      (.seq (.call (some (some (.local,ofString "bg"),none)) (ofString "hdr_uint_field")
        [.var .local (ofString "arr"),.const 22,.const 8])
        (.seq (.call (some (some (.local,ofString "w"),none)) (ofString "hdr_word_field")
          [.var .local (ofString "arr"),.const 22])
          (headerWordStore (ofString "w") 240))))

def decodeHeaderLegacySuffix : ProgHOL 64 :=
  .seq (headerExpressionStore (.const 0) 232) (headerExpressionStore (.const 0) 240)

theorem source_decode_header_current_suffix : decodeHeaderAt 56 =
    .seq (.ite decodeHeaderCurrentCondition decodeHeaderCurrentSuffix decodeHeaderLegacySuffix) (decodeHeaderAt 57) := rfl

theorem source_decode_header_return : decodeHeaderAt 57 = .return (.var .local (ofString "h")) := rfl

#print axioms source_decode_header_current_suffix
#print axioms source_decode_header_return
end InitECandidate.Runtime
