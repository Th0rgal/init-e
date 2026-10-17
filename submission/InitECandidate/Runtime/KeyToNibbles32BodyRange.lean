import InitECandidate.Runtime.KeyToNibbles32BodyBound
import InitECandidate.Runtime.KeyToNibbles32LoopRange
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original nibble conversion body for 32-byte trie keys uses
at most eight source ticks, without imposing any memory-success assumption. -/
theorem evaluate_keyToNibbles32_body_range {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (sourceDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 64 → state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (n : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))))
    (ticks : 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TrieNibbleRange post out 64) := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atN : entered.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "n" from by decide] using n
  obtain ⟨result,middle,run,cost,remaining,noTimeout,completed,noReturn⟩ :=
    evaluate_keyToNibbles32_main_loop entered initial atN ticks
  have enteredKey : entered.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "key" by decide] using keyLocal
  have enteredOut : entered.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "out" by decide] using outLocal
  obtain ⟨other,otherPost,rangeRun,_,_,_,rangeDone,_⟩ :=
    evaluate_keyToNibbles32_main_loop_range entered key out enteredKey enteredOut
      sourceDomain outputDomain initial atN ticks
  have same := rangeRun.symm.trans run
  have resultEq := (Prod.mk.inj same).1
  have postEq := (Prod.mk.inj same).2
  subst other
  subst otherPost
  have sequence : ∃ result post, evaluateHOLFiniteState entered
      (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))) = (result,post) ∧
      state.clock ≤ post.clock + 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TrieNibbleRange post out 64) := by
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      obtain ⟨⟨⟨index,atIndex,bounded,aligned⟩,localN⟩,zero⟩ := completed rfl
      have rankEq : keyToNibbles32Rank middle = 8 - index.toNat / 4 := by simp [keyToNibbles32Rank,atIndex]
      have equal : index = (32 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq
        change index.toNat = 32
        rw [rankEq] at zero
        omega
      have localI : middle.locals.lookup (ofString "i") = some (.val (.word (32 : BitVec 64))) := by simpa [equal] using atIndex
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780,evaluate_keyToNibbles32_tail_done middle localI localN]
      simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      refine ⟨_,_,rfl,cost,remaining,by simp,?_⟩
      intro value _
      exact (rangeDone rfl).after_frame rfl rfl rfl
    | some result =>
      refine ⟨_,_,rfl,cost,remaining,noTimeout,?_⟩
      intro value returned
      exact False.elim (noReturn value returned)
  obtain ⟨result,post,sequenceRun,total,remaining,noTimeout,range⟩ := sequence
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}) := by
    rw [source_keyToNibbles_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))); _) = _
    rw [sequenceRun]
  refine ⟨result,_,full,total,remaining,noTimeout,?_⟩
  intro value returned
  exact (range value returned).after_frame rfl rfl rfl

#print axioms evaluate_keyToNibbles32_body_range
end InitECandidate.Runtime
