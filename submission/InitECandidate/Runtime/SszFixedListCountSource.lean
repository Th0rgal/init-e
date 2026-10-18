import InitECandidate.Runtime.OriginalSszFixedListCountCode
import InitECandidate.Runtime.UdivmodBody
import InitECandidate.Runtime.SszFailCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Validation and return after the actual udivmod call. -/
def sszFixedListCountTail : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "qr"))) (.const 0))
      (.call (some (none,none)) (ofString "ssz_fail") [.const 30]) .skip)
    (.seq (.ite (.cmp .lower (.var .local (ofString "lim")) (.rfield 0 (.var .local (ofString "qr"))))
        (.call (some (none,none)) (ofString "ssz_fail") [.const 31]) .skip)
      (.return (.rfield 0 (.var .local (ofString "qr")))))

theorem source_sszFixedListCount_body : sourceFunctionBody Guest.guestFn_ssz_fixed_list_count =
    .decCall (ofString "qr") (.comb [.one,.one]) (ofString "udivmod")
      [.var .local (ofString "len"), .var .local (ofString "sz")] sszFixedListCountTail := by cbv

#print axioms source_sszFixedListCount_body
end InitECandidate.Runtime
