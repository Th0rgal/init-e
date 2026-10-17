import InitECandidate.Runtime.CompactNibbleByteScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_compactNibble_body : sourceFunctionBody Guest.guestFn_compact_to_nibbles =
    .seq (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
      (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) compactNibbleByteScope := by
  simp only [compactNibbleByteScope,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The full original decoder body on its nonempty-input path returns a
valid compact path within its explicit source-clock allocation. -/
theorem evaluate_compactNibble_nonempty_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd first : BitVec 64)
    (nonzero : length ≠ 0)
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
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_compact_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 5) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_byte_scope state pointer length out initial leaf c0 odd first byte byteValue loaded
      firstValue leafValue oddValue choice pointerLocal lengthLocal firstDomain lengthBound totalBound code
      sourceDomain outputDomain heapGlobal request finishBound ticks
  refine ⟨result,post,?_,cost,remaining,noTimeout,returned⟩
  rw [source_compactNibble_body,evaluateHOLFiniteState_seq_line780,check]
  exact run

#print axioms evaluate_compactNibble_nonempty_body
end InitECandidate.Runtime
