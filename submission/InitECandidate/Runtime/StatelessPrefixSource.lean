import InitECandidate.Runtime.StatelessInputSource
import InitECandidate.Runtime.SszLe32Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stFail (c : BitVec 64) : ProgHOL 64 := .call (some (none,none)) (ofString "ssz_fail") [.const c]
def stGuard0 : ProgHOL 64 := .ite (.cmp .lower (sszLocal "len") (.const 2)) (stFail 1) .skip
def stMagicCond : ExpHOL 64 :=
  .cmp .notEqual (.const 0) (.op .or [.cmp .notEqual (.loadByte (sszLocal "p")) (.const 21),
    .cmp .notEqual (.loadByte (.op .add [sszLocal "p", .const 1])) (.const 1)])
def stGuard1 : ProgHOL 64 := .ite stMagicCond (stFail 2) .skip
def stAssignP : ProgHOL 64 := .assign .local (ofString "p") (.op .add [sszLocal "p", .const 2])
def stAssignLen : ProgHOL 64 := .assign .local (ofString "len") (.op .sub [sszLocal "len", .const 2])
def stGuard4 : ProgHOL 64 := .ite (.cmp .lower (sszLocal "len") (.const 16)) (stFail 80) .skip
def stOffsetsGlobal : ExpHOL 64 := .var .global (ofString "ssz_offs")
def stSecondRead : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [sszLocal "p", .const 4]),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 4, .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 4, .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 4, .const 3])) (.const 24)]
def stStore0 : ProgHOL 64 := .store stOffsetsGlobal sszSplitFirst
def stStore1 : ProgHOL 64 := .store (.op .add [stOffsetsGlobal, .const 8]) stSecondRead
def stCheck : ProgHOL 64 :=
  .call (some (none,none)) (ofString "ssz_check_offsets") [stOffsetsGlobal, .const 2, .const 16, sszLocal "len"]

theorem source_stateless_prefix :
    statelessAt 0 = .seq stGuard0 (statelessAt 1) ∧ statelessAt 1 = .seq stGuard1 (statelessAt 2) ∧
    statelessAt 2 = .seq stAssignP (statelessAt 3) ∧ statelessAt 3 = .seq stAssignLen (statelessAt 4) ∧
    statelessAt 4 = .seq stGuard4 (statelessAt 5) ∧ statelessAt 5 = .seq stStore0 (statelessAt 6) ∧
    statelessAt 6 = .seq stStore1 (statelessAt 7) ∧ statelessAt 7 = .seq stCheck (statelessAt 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [statelessAt, statelessNext, sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl

theorem stSecondRead_bounded {σ : Type} (st : PanSemStateExact 64 σ) [DecidablePred st.memaddrs] :
    Bounded32 st stSecondRead :=
  bounded32_or4 st _ _ _ _ (bounded32_loadByte st _) (bounded32_shift st _ 8 (by decide))
    (bounded32_shift st _ 16 (by decide)) (bounded32_shift st _ 24 (by decide))

#print axioms source_stateless_prefix
end InitECandidate.Runtime
