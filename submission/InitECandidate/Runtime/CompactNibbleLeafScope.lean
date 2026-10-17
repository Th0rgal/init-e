import InitECandidate.Runtime.CompactNibbleOddScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleLeafScope : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ (.dec _ _ _ body)) => body
  | _ => .skip

theorem source_compactNibble_leaf_scope : compactNibbleLeafScope =
    .dec (ofString "is_leaf") .one
      (.op .and [.shift .lsr (.var .local (ofString "first")) (.const 1),.const 1]) compactNibbleOddScope := by
  simp only [compactNibbleLeafScope,compactNibbleOddScope,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Both flag declarations are evaluated from the actual compact header and
restored after the certified allocator and conversion continuation. -/
theorem evaluate_compactNibble_leaf_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd first : BitVec 64)
    (leafValue : leaf = (first >>> (1 : Nat)) &&& 1)
    (oddValue : odd = first &&& 1)
    (choice : initial = if odd = 0 then 0 else 1)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (byteLocal : state.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (firstLocal : state.locals.lookup (ofString "first") = some (.val (.word first)))
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
    ∃ result post, evaluateHOLFiniteState state compactNibbleLeafScope = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 5) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  let entered := setVarHOLFinite (ofString "is_leaf") (.val (.word leaf)) state
  have frame : ∀ name, name ≠ ofString "is_leaf" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have leafAt : entered.locals.lookup (ofString "is_leaf") = some (.val (.word leaf)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.shift .lsr (.var .local (ofString "first")) (.const 1),.const 1]) = some (.val (.word leaf)) := by
    rw [leafValue]
    simp [evalHOLExact,evalListHOLExact,firstLocal,wordShiftHOL,wordOpHOL,wordOp,valueIsWord,valueWord]
    change (first >>> (1 : Nat)) &&& ((1 : BitVec 64) &&& 18446744073709551615) = _
    bv_decide
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_odd_scope entered pointer length out initial leaf c0 odd first oddValue choice
      ((frame _ (by decide)).trans pointerLocal) ((frame _ (by decide)).trans lengthLocal) leafAt
      ((frame _ (by decide)).trans byteLocal) ((frame _ (by decide)).trans firstLocal)
      firstDomain lengthBound totalBound code sourceDomain outputDomain heapGlobal request finishBound ticks
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "is_leaf",state.locals.lookup (ofString "is_leaf"))}
  refine ⟨result,final,?_,cost,remaining,noTimeout,?_⟩
  · rw [source_compactNibble_leaf_scope,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered compactNibbleOddScope; _) = _
    rw [run]
  · intro value equal
    exact ⟨(returned value equal).1,(returned value equal).2.after_frame rfl rfl rfl⟩

#print axioms evaluate_compactNibble_leaf_scope
end InitECandidate.Runtime
