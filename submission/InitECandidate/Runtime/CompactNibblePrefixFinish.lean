import InitECandidate.Runtime.CompactNibbleFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose both compact-path branches with suffix conversion and the actual
structured return, preserving the original output length and source budget. -/
theorem evaluate_compactNibble_prefix_finish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf c0 odd : BitVec 64)
    (choice : initial = if odd = 0 then 0 else 1)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (initialLocal : state.locals.lookup (ofString "k") = some (.val (.word (0 : BitVec 64))))
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
    ∃ result post, evaluateHOLFiniteState state (.seq compactNibblePrefix compactNibbleFinish) = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 4) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  obtain ⟨middle,prefixRun,clock,kAt,valid,domain,codeEq,locals⟩ :=
    evaluate_compactNibble_prefix state out c0 odd outLocal byteLocal oddLocal initialLocal firstDomain
  have initialAt : middle.locals.lookup (ofString "k") = some (.val (.word initial)) := by
    simpa only [choice] using kAt
  have initialRange : TrieNibbleRange middle out initial := by simpa only [choice] using valid
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
    evaluate_compactNibble_finish middle pointer length out initial leaf
      ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal)
      ((locals _ (by decide)).trans outLocal) initialAt ((locals _ (by decide)).trans leafLocal)
      initialRange lengthBound totalBound (codeEq.trans code)
      (by simpa only [domain] using sourceDomain) (by simpa only [domain] using outputDomain)
      (by omega)
  refine ⟨result,post,?_,by omega,by omega,noTimeout,returned⟩
  rw [evaluateHOLFiniteState_seq_line780,prefixRun]
  exact run

#print axioms evaluate_compactNibble_prefix_finish
end InitECandidate.Runtime
