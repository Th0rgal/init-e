import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def le32Base (b : String) : ExpHOL 64 :=
  .op .or [.loadByte (sszLocal b),
    .shift .lsl (.loadByte (.op .add [sszLocal b, .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal b, .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal b, .const 3])) (.const 24)]

def le32Off (b : String) (k : BitVec 64) : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [sszLocal b, .const k]),
    .shift .lsl (.loadByte (.op .add [sszLocal b, .const k, .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal b, .const k, .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal b, .const k, .const 3])) (.const 24)]

def le64Slot : ExpHOL 64 :=
  .op .or [.loadByte (.op .add [sszLocal "p", .const 8]),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 8, .const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 8, .const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 8, .const 3])) (.const 24),
    .shift .lsl (.op .or [.loadByte (.op .add [sszLocal "p", .const 8, .const 4]),
      .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 8, .const 4, .const 1])) (.const 8),
      .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 8, .const 4, .const 2])) (.const 16),
      .shift .lsl (.loadByte (.op .add [sszLocal "p", .const 8, .const 4, .const 3])) (.const 24)]) (.const 32)]

def midCheck : ProgHOL 64 :=
  .call (some (none,none)) (ofString "ssz_check_offsets") [stOffsetsGlobal, .const 3, .const 44, sszLocal "nlen"]

theorem source_stateless_mid :
    statelessAt 8 = .dec (ofString "o_npr") .one (.load .one stOffsetsGlobal) (statelessAt 9) ∧
    statelessAt 9 = .dec (ofString "o_wit") .one (.load .one (.op .add [stOffsetsGlobal, .const 8])) (statelessAt 10) ∧
    statelessAt 10 = .decCall (ofString "si") .one (ofString "alloc") [.const 96] (statelessAt 11) ∧
    statelessAt 11 = .seq (.store (.op .add [sszLocal "si", .const 88]) le64Slot) (statelessAt 12) ∧
    statelessAt 12 = .dec (ofString "np") .one (.op .add [sszLocal "p", sszLocal "o_npr"]) (statelessAt 13) ∧
    statelessAt 13 = .dec (ofString "nlen") .one (.op .sub [sszLocal "o_wit", sszLocal "o_npr"]) (statelessAt 14) ∧
    statelessAt 14 = .seq (.ite (.cmp .lower (sszLocal "nlen") (.const 44)) (stFail 81) .skip) (statelessAt 15) ∧
    statelessAt 15 = .dec (ofString "o_pl") .one (le32Base "np") (statelessAt 16) ∧
    statelessAt 16 = .dec (ofString "o_vh") .one (le32Off "np" 4) (statelessAt 17) ∧
    statelessAt 17 = .dec (ofString "o_rq") .one (le32Off "np" 40) (statelessAt 18) ∧
    statelessAt 18 = .seq (.store stOffsetsGlobal (sszLocal "o_pl")) (statelessAt 19) ∧
    statelessAt 19 = .seq (.store (.op .add [stOffsetsGlobal, .const 8]) (sszLocal "o_vh")) (statelessAt 20) ∧
    statelessAt 20 = .seq (.store (.op .add [stOffsetsGlobal, .const 16]) (sszLocal "o_rq")) (statelessAt 21) ∧
    statelessAt 21 = .seq midCheck (statelessAt 22) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [statelessAt, statelessNext, sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl

section
variable {σ : Type} (st : PanSemStateExact 64 σ) [DecidablePred st.memaddrs]
theorem le32Base_bounded (b : String) : Bounded32 st (le32Base b) :=
  bounded32_or4 st _ _ _ _ (bounded32_loadByte st _) (bounded32_shift st _ 8 (by decide))
    (bounded32_shift st _ 16 (by decide)) (bounded32_shift st _ 24 (by decide))
theorem le32Off_bounded (b : String) (k : BitVec 64) : Bounded32 st (le32Off b k) :=
  bounded32_or4 st _ _ _ _ (bounded32_loadByte st _) (bounded32_shift st _ 8 (by decide))
    (bounded32_shift st _ 16 (by decide)) (bounded32_shift st _ 24 (by decide))
end

#print axioms source_stateless_mid
end InitECandidate.Runtime
