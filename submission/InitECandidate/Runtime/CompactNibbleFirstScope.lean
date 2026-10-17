import InitECandidate.Runtime.CompactNibbleLeafScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleFirstScope : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ body) => body
  | _ => .skip

theorem source_compactNibble_first_scope : compactNibbleFirstScope =
    .dec (ofString "first") .one (.shift .lsr (.var .local (ofString "c0")) (.const 4)) compactNibbleLeafScope := by
  simp only [compactNibbleFirstScope,compactNibbleLeafScope,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Header extraction uses the actual source shift and retains the complete
decoder continuation's returned-value and runtime contracts. -/
theorem evaluate_compactNibble_first_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd first : BitVec 64)
    (firstValue : first = c0 >>> (4 : Nat))
    (leafValue : leaf = (first >>> (1 : Nat)) &&& 1)
    (oddValue : odd = first &&& 1)
    (choice : initial = if odd = 0 then 0 else 1)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (byteLocal : state.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (firstDomain : state.memaddrs (panByteAlignHOL out))
    (lengthBound : 2 * (length - 1).toNat + 8 < 2^64)
    (totalBound : initial.toNat + 2 * (length - 1).toNat < 2^64)
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((pointer + 1) + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (request : 2 * length ≤ (33806089496 : BitVec 64) - out)
    (finishBound : (allocationEnd out (2 * length)).toNat ≤ 33806089496)
    (ticks : (length - 1).toNat / 4 + 5 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state compactNibbleFirstScope = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 5) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  let entered := setVarHOLFinite (ofString "first") (.val (.word first)) state
  have frame : ∀ name, name ≠ ofString "first" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have firstAt : entered.locals.lookup (ofString "first") = some (.val (.word first)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.shift .lsr (.var .local (ofString "c0")) (.const 4)) = some (.val (.word first)) := by
    simp [evalHOLExact,byteLocal,wordShiftHOL,firstValue]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_leaf_scope entered pointer length out initial leaf c0 odd first leafValue oddValue choice
      ((frame _ (by decide)).trans pointerLocal) ((frame _ (by decide)).trans lengthLocal)
      ((frame _ (by decide)).trans byteLocal) firstAt
      firstDomain lengthBound totalBound code sourceDomain outputDomain heapGlobal request finishBound ticks
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "first",state.locals.lookup (ofString "first"))}
  refine ⟨result,final,?_,cost,remaining,noTimeout,?_⟩
  · rw [source_compactNibble_first_scope,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered compactNibbleLeafScope; _) = _
    rw [run]
  · intro value equal
    exact ⟨(returned value equal).1,(returned value equal).2.after_frame rfl rfl rfl⟩

#print axioms evaluate_compactNibble_first_scope
end InitECandidate.Runtime
