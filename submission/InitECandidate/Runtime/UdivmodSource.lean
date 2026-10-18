import InitECandidate.Runtime.OriginalUdivmodCode
import InitECandidate.Runtime.UdivmodArith
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One restoring-division iteration of the actual udivmod loop. -/
def udivmodStep : ProgHOL 64 :=
  .seq (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
    (.seq (.assign .local (ofString "r") (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1),
        .op .and [.shift .lsr (.var .local (ofString "a")) (.var .local (ofString "i")), .const 1]]))
      (.ite (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "b")))
        (.seq (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "b")]))
          (.assign .local (ofString "q") (.op .or [.var .local (ofString "q"),
            .shift .lsl (.const 1) (.var .local (ofString "i"))])))
        .skip))

def udivmodLoop : ProgHOL 64 :=
  .while (.cmp .less (.const 0) (.var .local (ofString "i"))) udivmodStep

def udivmodTail : ProgHOL 64 :=
  .dec (ofString "q") .one (.const 0) (.dec (ofString "r") .one (.const 0) (.dec (ofString "i") .one (.const 64)
    (.seq udivmodLoop (.return (.rstruct [.var .local (ofString "q"), .var .local (ofString "r")])))))

theorem source_udivmod_body : sourceFunctionBody Guest.guestFn_udivmod =
    .seq (.ite (.cmp .equal (.var .local (ofString "b")) (.const 0))
        (.call (some (none,none)) (ofString "trap_with") [.const 2]) .skip)
      (.seq (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
          (.return (.rstruct [.const 0, .var .local (ofString "a")])) .skip)
        udivmodTail) := by cbv

#print axioms source_udivmod_body
end InitECandidate.Runtime
