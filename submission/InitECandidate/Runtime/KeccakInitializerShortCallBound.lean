import InitECandidate.Runtime.KeccakShortCallBound
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.MemzeroIntervalDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initializer hashes shorter than one Keccak block use the initialized
buffers. This includes the 33-byte EVM transfer-topic hash and early exits. -/
theorem evaluate_keccak_initializer_short_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sourceArgument sizeArgument outputArgument : ExpHOL 64) (source size output : BitVec 64)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 359 ≤ state.clock)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [sourceArgument,sizeArgument,outputArgument] = some [.val (.word source),.val (.word size),.val (.word output)])
    (shortInput : size.toNat < 136) (sourceAbove : 2713714688 ≤ source.toNat)
    (sourceFits : source.toNat + size.toNat ≤ 33806089496)
    (sourceAligned : source.toNat % 8 = 0) (outputAligned : output.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256")
      [sourceArgument,sizeArgument,outputArgument])
    state.clock ≤ evaluated.2.clock + size.toNat + 359 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.2.globals = state.globals ∧
      evaluated.2.code = state.code ∧ evaluated.2.memaddrs = state.memaddrs := by
  have stateDomains := memzero_interval_domains state 2713714976 200 (by decide) (by decide)
    (by intro address lower upper; apply arena address <;> change 2713714976 ≤ address.toNat at lower
        <;> change address.toNat < 2713714976 + 200 at upper <;> omega)
  have padDomains := memzero_interval_domains state 2713715176 136 (by decide) (by decide)
    (by intro address lower upper; apply arena address <;> change 2713715176 ≤ address.toNat at lower
        <;> change address.toNat < 2713715176 + 136 at upper <;> omega)
  have sourceDomains := memzero_interval_domains state source size sourceAligned (by omega)
    (by intro address lower upper; apply arena address <;> omega)
  have bounded := evaluate_keccak_short_call_bounded state sourceArgument sizeArgument outputArgument
    2713714976 2713715176 source size output stateGlobal padGlobal code budget args
    (by decide) (by decide) stateDomains.1 stateDomains.2 (by decide) (by decide)
    sourceAligned outputAligned (by omega) padDomains.1 padDomains.2 sourceDomains.1 sourceDomains.2
  have globals := keccak_call_globals_frame [sourceArgument,sizeArgument,outputArgument] state code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "keccak256")
    [sourceArgument,sizeArgument,outputArgument])
  exact ⟨bounded.1,bounded.2.1,bounded.2.2,globals,metadata.1,metadata.2.1⟩

#print axioms evaluate_keccak_initializer_short_call_bounded
end InitECandidate.Runtime
