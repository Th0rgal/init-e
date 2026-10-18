import InitECandidate.Runtime.StatelessPrefixSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def wsGuard : ProgHOL 64 := .ite (.cmp .lower (sszLocal "wlen") (.const 12)) (stFail 82) .skip
def wsIndex4 : ExpHOL 64 := .panop .mul [sszLocal "i", .const 4]
def wsRead : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [sszLocal "wp", wsIndex4]),
    .shift .lsl (.loadByte (.op .add [sszLocal "wp", wsIndex4, .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal "wp", wsIndex4, .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal "wp", wsIndex4, .const 3])) (.const 24)]
def wsBody : ProgHOL 64 :=
  .seq (.store (.op .add [stOffsetsGlobal, .panop .mul [sszLocal "i", .const 8]]) wsRead)
    (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1]))
def wsLoop : ProgHOL 64 := .while (.cmp .less (sszLocal "i") (.const 3)) wsBody

theorem source_stateless_witness_setup :
    statelessAt 32 = .seq wsGuard (statelessAt 33) ∧
    statelessAt 33 = .dec (ofString "i") .one (.const 0) (statelessAt 34) ∧
    statelessAt 34 = .seq wsLoop (statelessAt 35) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [statelessAt, statelessNext, sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl

theorem wsRead_bounded {σ : Type} (st : PanSemStateExact 64 σ) [DecidablePred st.memaddrs] : Bounded32 st wsRead :=
  bounded32_or4 st _ _ _ _ (bounded32_loadByte st _) (bounded32_shift st _ 8 (by decide))
    (bounded32_shift st _ 16 (by decide)) (bounded32_shift st _ 24 (by decide))

#print axioms source_stateless_witness_setup
end InitECandidate.Runtime
