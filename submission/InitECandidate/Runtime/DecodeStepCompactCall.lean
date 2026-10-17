import InitECandidate.Runtime.CompactNibbleCallResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepCompactCall : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__decode_step with
  | .dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.decCall _ _ _ _ (.dec _ _ _
      (.seq (.ite _ (.decCall _ _ _ _ (.seq _ body)) _) _)))))) => body
  | _ => .skip

def decodeStepCompactContinuation : ProgHOL 64 :=
  match decodeStepCompactCall with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_decodeStep_compact_call : decodeStepCompactCall =
    .decCall (ofString "cn") (.comb [.one,.one,.one]) (ofString "compact_to_nibbles")
      [.rfield 1 (.var .local (ofString "pi")),.rfield 2 (.var .local (ofString "pi"))]
      decodeStepCompactContinuation := by
  simp only [decodeStepCompactCall,decodeStepCompactContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original trie parser receives a valid decoded segment at its actual
cn declaration, rather than relying on a caller-supplied segment certificate. -/
theorem evaluate_decodeStep_compact_call {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length out : BitVec 64)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (kind consumed : BitVec 64)
    (itemLocal : state.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < length.toNat →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat →
      state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (request : 2 * length ≤ (33806089496 : BitVec 64) - out)
    (finishBound : (allocationEnd out (2 * length)).toNat ≤ 33806089496)
    (ticks : length.toNat / 4 + 6 ≤ state.clock)
    (run : evaluateHOLFiniteState state decodeStepCompactCall = (none,post)) :
    ∃ (count leaf : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ 2 * length.toNat ∧ leaf.toNat ≤ 1 ∧ TrieNibbleRange ready out count ∧
      ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "cn")
        (.rStruct [.val (.word out),.val (.word count),.val (.word leaf)]) ready)
        decodeStepCompactContinuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "cn",state.locals.lookup (ofString "cn"))} := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.rfield 1 (.var .local (ofString "pi")),.rfield 2 (.var .local (ofString "pi"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,itemLocal]
  rw [source_decodeStep_compact_call] at run
  exact evaluate_compactNibble_decCall_normal state post (ofString "cn")
    [.rfield 1 (.var .local (ofString "pi")),.rfield 2 (.var .local (ofString "pi"))]
    decodeStepCompactContinuation pointer length out lengthBound args code sourceDomain outputDomain
    heapGlobal request finishBound ticks run

#print axioms evaluate_decodeStep_compact_call
end InitECandidate.Runtime
