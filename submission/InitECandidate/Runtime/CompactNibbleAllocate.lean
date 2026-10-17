import InitECandidate.Runtime.CompactNibbleAfterAlloc
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleAllocate : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ body)))) => body
  | _ => .skip

theorem source_compactNibble_allocate : compactNibbleAllocate =
    .decCall (ofString "out") .one (ofString "alloc")
      [.panop .mul [.const 2,.var .local (ofString "n")]] compactNibbleAfterAlloc := by
  simp only [compactNibbleAllocate,compactNibbleAfterAlloc,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The real allocator declaration and decoder continuation produce a valid
compact path at the returned allocation pointer within the source budget. -/
theorem evaluate_compactNibble_allocate {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd : BitVec 64)
    (choice : initial = if odd = 0 then 0 else 1)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
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
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (request : 2 * length ≤ (33806089496 : BitVec 64) - out)
    (finishBound : (allocationEnd out (2 * length)).toNat ≤ 33806089496)
    (ticks : (length - 1).toNat / 4 + 5 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state compactNibbleAllocate = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 5) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.const 2,.var .local (ofString "n")]] = some [.val (.word (2 * length))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,lengthLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,_,clock,memory,locals,postCode,domain,_,endian,_,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.panop .mul [.const 2,.var .local (ofString "n")])
      out (2 * length) args code (by omega) heapGlobal request finishBound
  let entered := setVarHOLFinite (ofString "out") (.val (.word out)) ready
  have frame : ∀ name, name ≠ ofString "out" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atOut : entered.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_after_alloc entered pointer length out initial leaf c0 odd choice
      ((frame _ (by decide)).trans pointerLocal) ((frame _ (by decide)).trans lengthLocal) atOut
      ((frame _ (by decide)).trans leafLocal) ((frame _ (by decide)).trans byteLocal)
      ((frame _ (by decide)).trans oddLocal) (by simpa only [entered,setVarHOLFinite,domain] using firstDomain)
      lengthBound totalBound (postCode.trans code)
      (by simpa only [entered,setVarHOLFinite,domain] using sourceDomain)
      (by simpa only [entered,setVarHOLFinite,domain] using outputDomain)
      (by change (length - 1).toNat / 4 + 4 ≤ ready.clock; omega)
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "out",state.locals.lookup (ofString "out"))}
  have entryClock : entered.clock = state.clock - 1 := clock
  refine ⟨result,final,?_,by change state.clock ≤ post.clock + _; omega,by change post.clock ≤ state.clock; omega,noTimeout,?_⟩
  · rw [source_compactNibble_allocate,declaration]
    change (let output := evaluateHOLFiniteState entered compactNibbleAfterAlloc; _) = _
    rw [run]
  · intro value equal
    exact ⟨(returned value equal).1,(returned value equal).2.after_frame rfl rfl rfl⟩

#print axioms evaluate_compactNibble_allocate
end InitECandidate.Runtime
