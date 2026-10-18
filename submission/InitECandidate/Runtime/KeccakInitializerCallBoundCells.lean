import InitECandidate.Runtime.KeccakInitializerCallBound
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.AlignedCellDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_keccak_initializer_call_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sourceArgument sizeArgument outputArgument : ExpHOL 64) (source size output : BitVec 64)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 359 ≤ state.clock)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [sourceArgument,sizeArgument,outputArgument] = some [.val (.word source),.val (.word size),.val (.word output)])
    (tiny : size.toNat ≤ 1) (sourceAbove : 2713714688 ≤ source.toNat)
    (sourceFits : source.toNat + size.toNat ≤ 33806089496)
    (sourceAligned : source.toNat % 8 = 0) (outputAligned : output.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256")
      [sourceArgument,sizeArgument,outputArgument])
    state.clock ≤ evaluated.2.clock + size.toNat + 359 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.2.globals = state.globals ∧
      evaluated.2.code = state.code ∧ evaluated.2.memaddrs = state.memaddrs := by
  have stateDomains := aligned_interval_byte_domains state 2713714976 200 (by decide) (by decide)
    (by intro address aligned lower upper; apply arena address aligned <;> change 2713714976 ≤ address.toNat at lower
        <;> change address.toNat < 2713714976 + 200 at upper <;> omega)
  have padDomains := aligned_interval_byte_domains state 2713715176 136 (by decide) (by decide)
    (by intro address aligned lower upper; apply arena address aligned <;> change 2713715176 ≤ address.toNat at lower
        <;> change address.toNat < 2713715176 + 136 at upper <;> omega)
  have sourceDomains := aligned_interval_byte_domains state source size sourceAligned (by omega)
    (by intro address aligned lower upper; apply arena address aligned <;> omega)
  have bounded := evaluate_keccak_short_call_bounded_cells state sourceArgument sizeArgument outputArgument
    2713714976 2713715176 source size output stateGlobal padGlobal code budget args
    (by decide) (by decide) stateDomains (by decide) (by decide)
    sourceAligned outputAligned (by omega) padDomains sourceDomains
  have globals := keccak_call_globals_frame [sourceArgument,sizeArgument,outputArgument] state code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "keccak256")
    [sourceArgument,sizeArgument,outputArgument])
  exact ⟨bounded.1,bounded.2.1,bounded.2.2,globals,metadata.1,metadata.2.1⟩

#print axioms evaluate_keccak_initializer_call_bounded_cells
end InitECandidate.Runtime
