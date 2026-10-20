import InitECandidate.Runtime.KeccakWideFullBodyBound
import InitECandidate.Runtime.KeccakShortCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every installed Keccak call over an input within the wide nonwrap cap is
bounded, including full blocks and failed accesses. Only output alignment
and the two typed global workspace pointers are required. -/
theorem runBounded_keccak_wide_full_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word source),.val (.word size),.val (.word output)])
    (small : size.toNat ≤ 2^62) (outAligned : output.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode) (budget : (size.toNat * 20 + 124) + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "keccak256") arguments) ((size.toNat * 20 + 124) + 1) := by
  refine RunBounded.call args budget ?_
  intro body callee returnShape lookup
  have installed : state.code.lookup (ofString "keccak256") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_keccak256,.one) := by
    rw [code]
    exact originalRuntimeCode_keccak_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_keccak256) source size output (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word source))).update (ofString "n",.val (.word size))).update
      (ofString "out",.val (.word output)))
  exact runBounded_keccak_wide_full_body entry pointer pad source size output atState atPad
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small outAligned code
    (by change size.toNat * 20 + 124 ≤ state.clock - 1; omega)

#print axioms runBounded_keccak_wide_full_call
end InitECandidate.Runtime
