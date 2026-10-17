import InitECandidate.Runtime.KeccakShortBodyBound
import InitECandidate.Runtime.OriginalKeccakCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real call into the original Keccak code costs at most n+359 source
ticks for aligned short inputs and outputs, including early exceptional exits. -/
theorem evaluate_keccak_short_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sourceArgument sizeArgument outputArgument : ExpHOL 64)
    (pointer pad source size output : BitVec 64)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 359 ≤ state.clock)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [sourceArgument,sizeArgument,outputArgument] = some [.val (.word source),.val (.word size),.val (.word output)])
    (stateSmall : pointer.toNat + 200 ≤ 33806089496)
    (stateAligned : pointer.toNat % 8 = 0)
    (stateWords : ∀ offset : Nat, offset < 200 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (stateBytes : ∀ offset : Nat, offset < 200 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (small : pad.toNat + 136 ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (outputAligned : output.toNat % 8 = 0)
    (shortInput : size.toNat < 136)
    (words : ∀ offset : Nat, offset < 136 → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < 136 → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") [sourceArgument,sizeArgument,outputArgument]);
    state.clock ≤ evaluated.2.clock + size.toNat + 359 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word source))).update (ofString "n",.val (.word size))).update (ofString "out",.val (.word output))
  let entry := callEntryStateHOLFinite state callee
  have localP : entry.locals.lookup (ofString "p") = some (.val (.word source)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "out" ≠ ofString "p" from by decide,show ofString "n" ≠ ofString "p" from by decide]
  have localN : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "out" ≠ ofString "n" from by decide]
  have localOut : entry.locals.lookup (ofString "out") = some (.val (.word output)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,cost,remaining,noTimeout⟩ := evaluate_keccak_short_body_bounded entry pointer pad source size output
    stateGlobal padGlobal localP localN localOut code (by change size.toNat + 358 ≤ state.clock - 1; omega)
    stateSmall stateAligned stateWords stateBytes small padAligned sourceAligned outputAligned shortInput
    words bytes sourceWords sourceBytes
  have postCost : state.clock ≤ post.clock + size.toNat + 359 := by
    change state.clock - 1 ≤ post.clock + size.toNat + 358 at cost
    omega
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  have installed : state.code.lookup (ofString "keccak256") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_keccak256,.one) := by
    rw [code]
    exact originalRuntimeCode_keccak_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_keccak256) source size output (by decide) (by decide) (by decide) installed
  have nonzero : state.clock ≠ 0 := by omega
  simp only [evaluateHOLFiniteState_call,args]
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,body]
  cases result with
  | none => exact ⟨postCost,postRemaining,by simp⟩
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp_all

#print axioms evaluate_keccak_short_call_bounded
end InitECandidate.Runtime
