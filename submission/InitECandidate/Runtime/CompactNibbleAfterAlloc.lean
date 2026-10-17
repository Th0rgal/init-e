import InitECandidate.Runtime.CompactNibblePrefixFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleAfterAlloc : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ body))))) => body
  | _ => .skip

theorem source_compactNibble_after_alloc : compactNibbleAfterAlloc =
    .dec (ofString "k") .one (.const 0) (.seq compactNibblePrefix compactNibbleFinish) := by
  simp only [compactNibbleAfterAlloc,compactNibblePrefix,compactNibbleFinish,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original continuation after allocating output, including
its local counter declaration, returns the certified compact path. -/
theorem evaluate_compactNibble_after_alloc {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd : BitVec 64)
    (choice : initial = if odd = 0 then 0 else 1)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (leafLocal : state.locals.lookup (ofString "is_leaf") = some (.val (.word leaf)))
    (byteLocal : state.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (oddLocal : state.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (firstDomain : state.memaddrs (panByteAlignHOL out))
    (lengthBound : 2 * (length - 1).toNat + 8 < 2^64)
    (totalBound : initial.toNat + 2 * (length - 1).toNat < 2^64)
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((pointer + 1) + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset)))
    (ticks : (length - 1).toNat / 4 + 4 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state compactNibbleAfterAlloc = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 4) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  let entered := setVarHOLFinite (ofString "k") (.val (.word (0 : BitVec 64))) state
  have locals : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atK : entered.locals.lookup (ofString "k") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_prefix_finish entered pointer length out initial leaf c0 odd choice
      ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal)
      ((locals _ (by decide)).trans outLocal) atK ((locals _ (by decide)).trans leafLocal)
      ((locals _ (by decide)).trans byteLocal) ((locals _ (by decide)).trans oddLocal)
      firstDomain lengthBound totalBound code sourceDomain outputDomain ticks
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "k",state.locals.lookup (ofString "k"))}
  refine ⟨result,final,?_,cost,remaining,noTimeout,?_⟩
  · rw [source_compactNibble_after_alloc,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (.seq compactNibblePrefix compactNibbleFinish); _) = _
    rw [run]
  · intro value equal
    exact ⟨(returned value equal).1,(returned value equal).2.after_frame rfl rfl rfl⟩

#print axioms evaluate_compactNibble_after_alloc
end InitECandidate.Runtime
