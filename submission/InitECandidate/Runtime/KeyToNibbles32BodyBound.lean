import InitECandidate.Runtime.KeyToNibbles32MainBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- For a 32-byte trie key the original byte-at-a-time tail is skipped. -/
theorem evaluate_keyToNibbles32_tail_done {F : Type} (state : PanSemStateFiniteExact 64 F)
    (i : state.locals.lookup (ofString "i") = some (.val (.word (32 : BitVec 64))))
    (n : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64)))) :
    evaluateHOLFiniteState state keyToNibblesTailLoop = (none,state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,i,n,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_keyToNibbles_tail_loop,evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rfl

/-- The complete original nibble conversion body for 32-byte trie keys uses
at most eight source ticks, without imposing any memory-success assumption. -/
theorem evaluate_keyToNibbles32_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (n : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))))
    (ticks : 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atN : entered.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "n" from by decide] using n
  obtain ⟨result,middle,run,cost,remaining,noTimeout,completed,_⟩ :=
    evaluate_keyToNibbles32_main_loop entered initial atN ticks
  have sequence : ∃ result post, evaluateHOLFiniteState entered
      (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))) = (result,post) ∧
      state.clock ≤ post.clock + 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
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
      exact ⟨_,_,rfl,cost,remaining,by simp⟩
    | some result => exact ⟨_,_,rfl,cost,remaining,noTimeout⟩
  obtain ⟨result,post,sequenceRun,total,remaining,noTimeout⟩ := sequence
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}) := by
    rw [source_keyToNibbles_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))); _) = _
    rw [sequenceRun]
  exact ⟨result,_,full,total,remaining,noTimeout⟩

#print axioms evaluate_keyToNibbles32_tail_done
#print axioms evaluate_keyToNibbles32_body_bounded
end InitECandidate.Runtime
