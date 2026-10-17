import InitECandidate.Runtime.CompactNibbleBodyBound
import InitECandidate.Runtime.OriginalCompactNibbleCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.PanDecCallNormalBodyScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original decoder declaration-call exposes a bounded
valid path in the caller's continuation, using the callee's actual output memory. -/
theorem evaluate_compactNibble_decCall_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer length out : BitVec 64)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < length.toNat →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat →
      state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (request : 2 * length ≤ (33806089496 : BitVec 64) - out)
    (finishBound : (allocationEnd out (2 * length)).toNat ≤ 33806089496)
    (ticks : length.toNat / 4 + 6 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one,.one])
      (ofString "compact_to_nibbles") arguments continuation) = (none,post)) :
    ∃ (count leaf : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ 2 * length.toNat ∧ leaf.toNat ≤ 1 ∧ TrieNibbleRange ready out count ∧
      ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word out),.val (.word count),.val (.word leaf)]) ready)
        continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,_,_,_,returned⟩ := evaluate_compactNibble_body_bounded entry pointer length out
    lengthBound pointerLocal lengthLocal code sourceDomain outputDomain heapGlobal request finishBound
    (by change length.toNat / 4 + 5 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "compact_to_nibbles") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_compact_to_nibbles,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_compactNibble_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
    (.comb [.one,.one,.one]) pointer length (by decide) installed
  obtain ⟨value,actual,ready,output,actualRun,locals,memory,domain,endian,tail,restored⟩ :=
    evaluate_decCall_normal_body_scope state post name (ofString "compact_to_nibbles")
      (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments [.val (.word pointer),.val (.word length)]
      (sourceFunctionBody Guest.guestFn_compact_to_nibbles) continuation callee args lookup run
  have same := Prod.mk.inj (bodyRun.symm.trans actualRun)
  have actualEq : bodyPost = actual := same.2
  subst actual
  obtain ⟨count,leaf,valueEq,countBound,leafBound,valid⟩ := returned value same.1
  subst value
  exact ⟨count,leaf,ready,output,countBound,leafBound,valid.after_frame memory domain endian,locals,tail,restored⟩

#print axioms evaluate_compactNibble_decCall_normal
end InitECandidate.Runtime
