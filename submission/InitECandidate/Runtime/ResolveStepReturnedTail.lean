import InitECandidate.Runtime.ResolveStepTerminal
import InitECandidate.Runtime.ResolveStepLookupBound
import InitECandidate.Runtime.NodedbLookupReturnedSlice
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.TwoWordValueShape
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanReturnedPath
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ResolveStepResultSpan (input inputLength : BitVec 64) (value : ValueHOL 64) : Prop :=
  ∃ flag pointer length hash : BitVec 64,
    value = .rStruct [.val (.word flag),.val (.word pointer),.val (.word length),.val (.word hash)] ∧
    (flag = 0 ∨ flag = 1) ∧
    (flag = 1 → input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
      pointer.toNat + length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat)

private theorem seq_returned_terminal_first {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (value : ValueHOL 64)
    (terminal : (evaluateHOLFiniteState s first).1 ≠ none)
    (run : evaluateHOLFiniteState s (.seq first tail) = (some (.returned value),post)) :
    evaluateHOLFiniteState s first = (some (.returned value),post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState s first with
  | mk result middle =>
    rw [firstRun] at run terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped => exact run

theorem resolve_step_hashed_returned_result {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind key payload consumed input inputLength : BitVec 64)
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s resolveStepHashed = (some (.returned value),post)) :
    ResolveStepResultSpan input inputLength value := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "it"))] = some [.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atItem]
  have lookup := pan_single_word_lookup s.code.lookup (ofString "node_new_hashed") (ofString "hash")
    (sourceFunctionBody Guest.guestFn_node_new_hashed) key
    (by rw [code]; exact originalRuntimeCode_nodeNewHashed_lookup)
  rw [source_resolve_step_hashed] at run
  obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "hn") (ofString "node_new_hashed") .one .one
      _ _ (sourceFunctionBody Guest.guestFn_node_new_hashed) _
      (HolFiniteMapExact.empty.update (ofString "hash",.val (.word key))) value args lookup run
  obtain ⟨node,rfl⟩ := value_word_of_shape_one returned ((shapeEqHOL_eq_true _ _).mp checked.1)
  have actual : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "hn") (.val (.word node)) {bodyPost with locals := s.locals})
      (.return (.rstruct [.const 0,.var .local (ofString "hn"),.const 0,.const 0])) =
      (some (.returned (.rStruct [.val (.word (0#64)),.val (.word node),.val (.word (0#64)),.val (.word (0#64))])),
        emptyLocalsHOLFinite (setVarHOLFinite (ofString "hn") (.val (.word node)) {bodyPost with locals := s.locals})) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact]
  have eq := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (tailRun.symm.trans actual)))
  exact ⟨0,node,0,0,eq,Or.inl rfl,by simp⟩

theorem resolve_step_lookup_tail_returned_result {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind key payload consumed input inputLength : BitVec 64) (result value : ValueHOL 64)
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (atResult : s.locals.lookup (ofString "r") = some result)
    (resultSpan : result = .rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))] ∨
      ∃ pointer length : BitVec 64,
        result = .rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length)] ∧
        input.toNat ≤ pointer.toNat ∧ pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat ∧
        pointer.toNat+length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s resolveStepLookupTail = (some (.returned value),post)) :
    ResolveStepResultSpan input inputLength value := by
  rcases resultSpan with rfl | ⟨pointer,length,rfl,lo,hi,nowrap,small⟩
  · have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) resolveStepHashed .skip) =
        evaluateHOLFiniteState s resolveStepHashed := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atResult,Compiler.Encoders.Asm.wordCmpHOL]
    rw [source_resolve_step_lookup_tail] at run
    rw [evaluateHOLFiniteState_seq_line780,branch] at run
    cases called : evaluateHOLFiniteState s resolveStepHashed with
    | mk result middle =>
      rw [called] at run
      have terminal := resolve_step_hashed_terminal s
      rw [called] at terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped =>
        exact resolve_step_hashed_returned_result s post kind key payload consumed input inputLength atItem code value
          (called.trans run)
  · have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) resolveStepHashed .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atResult,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_lookup_tail,evaluateHOLFiniteState_seq_line780,branch] at run
    have actual : evaluateHOLFiniteState s
        (.return (.rstruct [.const 1,.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r")),.rfield 1 (.var .local (ofString "it"))])) =
        (some (.returned (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word key)])),
          emptyLocalsHOLFinite s) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atResult,atItem,shapeOfHOLExact]
    have eq := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (run.symm.trans actual)))
    exact ⟨1,pointer,length,key,eq,Or.inr rfl,fun _ => ⟨lo,hi,nowrap,small⟩⟩

#print axioms resolve_step_hashed_returned_result
#print axioms resolve_step_lookup_tail_returned_result
end InitECandidate.Runtime
