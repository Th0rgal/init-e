import InitECandidate.Runtime.MemcpyWideBodyBound
import InitECandidate.Runtime.OriginalMemcpyCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original memcpy discard calls add one clock to the body budget. -/
theorem evaluate_memcpy_call_wide_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (destination source size : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word destination),.val (.word source),.val (.word size)])
    (code : state.code = originalRuntimeCode) (small : size.toNat ≤ 2^62)
    (budget : size.toNat / 32 + size.toNat / 8 + 11 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments)
    state.clock ≤ evaluated.2.clock + (size.toNat / 32 + size.toNat / 8 + 11) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update
      (ofString "src",.val (.word source))).update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have dst : entry.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide,show ofString "src" ≠ ofString "dst" by decide]
  have src : entry.locals.lookup (ofString "src") = some (.val (.word source)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "n" ≠ ofString "src" by decide]
  have n : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_memcpy_body_wide_bounded entry destination source size dst src n small
    (by change size.toNat / 32 + size.toNat / 8 + 10 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
    rw [code]; exact originalRuntimeCode_memcpy_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memcpy) destination source size (by decide) (by decide) (by decide) installed
  have clock := evaluate_discard_call_body_clock state post (ofString "memcpy") arguments
    [.val (.word destination),.val (.word source),.val (.word size)] (sourceFunctionBody Guest.guestFn_memcpy) callee .one result args lookup (by omega) run
  have safe := evaluate_discard_call_body_no_timeout state post (ofString "memcpy") arguments
    [.val (.word destination),.val (.word source),.val (.word size)] (sourceFunctionBody Guest.guestFn_memcpy) callee .one result args lookup (by omega) run noTimeout
  dsimp only
  rw [clock]
  have entryClock : entry.clock = state.clock - 1 := rfl
  exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_memcpy_call_wide_bounded
end InitECandidate.Runtime
