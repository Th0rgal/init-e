import InitECandidate.Runtime.CompactNibbleFirstScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleByteScope : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ body => body
  | _ => .skip

theorem source_compactNibble_byte_scope : compactNibbleByteScope =
    .dec (ofString "c0") .one (.loadByte (.var .local (ofString "p"))) compactNibbleFirstScope := by
  simp only [compactNibbleByteScope,compactNibbleFirstScope,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Loading the actual header byte completes the normal decoder path from
its input pointer through flags, allocation, conversion and structured return. -/
theorem evaluate_compactNibble_byte_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd first : BitVec 64)
    (byte : UInt8)
    (byteValue : c0 = BitVec.ofNat 64 byte.toNat)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (firstValue : first = c0 >>> (4 : Nat))
    (leafValue : leaf = (first >>> (1 : Nat)) &&& 1)
    (oddValue : odd = first &&& 1)
    (choice : initial = if odd = 0 then 0 else 1)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
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
    ∃ result post, evaluateHOLFiniteState state compactNibbleByteScope = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 5) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  let entered := setVarHOLFinite (ofString "c0") (.val (.word c0)) state
  have frame : ∀ name, name ≠ ofString "c0" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have byteAt : entered.locals.lookup (ofString "c0") = some (.val (.word c0)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.var .local (ofString "p"))) = some (.val (.word c0)) := by
    simp [evalHOLExact,pointerLocal,loaded,byteValue]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_first_scope entered pointer length out initial leaf c0 odd first firstValue leafValue oddValue choice
      ((frame _ (by decide)).trans pointerLocal) ((frame _ (by decide)).trans lengthLocal) byteAt
      firstDomain lengthBound totalBound code sourceDomain outputDomain heapGlobal request finishBound ticks
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "c0",state.locals.lookup (ofString "c0"))}
  refine ⟨result,final,?_,cost,remaining,noTimeout,?_⟩
  · rw [source_compactNibble_byte_scope,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered compactNibbleFirstScope; _) = _
    rw [run]
  · intro value equal
    exact ⟨(returned value equal).1,(returned value equal).2.after_frame rfl rfl rfl⟩

#print axioms evaluate_compactNibble_byte_scope
end InitECandidate.Runtime
