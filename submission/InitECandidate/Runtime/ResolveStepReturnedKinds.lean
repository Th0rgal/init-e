import InitECandidate.Runtime.ResolveStepLookupResult
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem resolve_step_string_returned_result {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table heap total array kind key payload consumed input inputLength : BitVec 64)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s resolveStepStringBranch = (some (.returned value),post)) :
    ResolveStepResultSpan input inputLength value := by
  by_cases empty : payload = 0
  · subst payload
    have actual : evaluateHOLFiniteState s resolveStepStringBranch =
        (some (.returned (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))])),
          emptyLocalsHOLFinite s) := by
      rw [source_resolve_step_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,evalListHOLExact,shapeOfHOLExact]
    have eq := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (run.symm.trans actual)))
    exact ⟨0,0,0,0,eq,Or.inl rfl,by simp⟩
  · have guard : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0))
          (.return (.rstruct [.const 0,.const 0,.const 0,.const 0])) .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
        show payload ≠ 0#64 from empty,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_string,evaluateHOLFiniteState_seq_line780,guard] at run
    obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
      (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
    have same := mpt_fail_guard_normal_state s next _ 10 code normal
    subst next
    exact resolve_step_lookup_returned_result s post table heap total array kind key payload consumed input inputLength
      built entries slices atTable atItem code value tailRun

theorem resolve_step_kind_returned_result {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length table heap total array kind key payload consumed input inputLength : BitVec 64)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanNoWrap : pointer.toNat+length.toNat < 2^64) (spanSize : length.toNat ≤ inputLength.toNat)
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (resolveStepAt 3) = (some (.returned value),post)) :
    ResolveStepResultSpan input inputLength value := by
  by_cases zero : kind = 0
  · subst kind
    have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0)) resolveStepStringBranch .skip) =
        evaluateHOLFiniteState s resolveStepStringBranch := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL]
    rw [source_resolve_step_kind,evaluateHOLFiniteState_seq_line780,branch] at run
    cases firstRun : evaluateHOLFiniteState s resolveStepStringBranch with
    | mk result middle =>
      rw [firstRun] at run
      have terminal := resolve_step_string_terminal s
      rw [firstRun] at terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped =>
        exact resolve_step_string_returned_result s post table heap total array 0 key payload consumed input inputLength
          built entries slices atTable atItem code value (firstRun.trans run)
  · have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0)) resolveStepStringBranch .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
        show kind ≠ 0#64 from zero,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_kind,evaluateHOLFiniteState_seq_line780,branch] at run
    have actual : evaluateHOLFiniteState s
        (.return (.rstruct [.const 1,.var .local (ofString "p"),.var .local (ofString "n"),.const 0])) =
        (some (.returned (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word (0#64))])),
          emptyLocalsHOLFinite s) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atPointer,atLength,shapeOfHOLExact]
    have eq := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (run.symm.trans actual)))
    exact ⟨1,pointer,length,0,eq,Or.inr rfl,fun _ => ⟨spanLo,spanHi,spanNoWrap,spanSize⟩⟩

#print axioms resolve_step_string_returned_result
#print axioms resolve_step_kind_returned_result
end InitECandidate.Runtime
