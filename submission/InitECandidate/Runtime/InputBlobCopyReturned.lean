import InitECandidate.Runtime.InputBlobControl
import InitECandidate.Runtime.SharedLoadGlobalFrame
import InitECandidate.Runtime.NormalWhileInvariantByControl
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem inputBlob_loop_normal_bindings {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length index : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state inputBlobLoop = (none,post)) :
    post.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
      post.locals.lookup (ofString "len") = some (.val (.word length)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    current.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
    current.locals.lookup (ofString "len") = some (.val (.word length))
  have step : ∀ current next, invariant current →
      evaluateHOLFiniteState current inputBlobStep = (none,next) → invariant next := by
    rintro current next ⟨i,localIndex,localPointer,localLength⟩ normalRun
    obtain ⟨result,output,actual,_,locals,normal⟩ := evaluate_inputBlob_step current i localIndex
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (actual.symm.trans normalRun)
    rcases normal with ⟨_,advanced⟩ | impossible | ⟨event,impossible⟩
    · exact ⟨i + 8,advanced,(locals rfl _ (by decide) (by decide)).trans localPointer,
        (locals rfl _ (by decide) (by decide)).trans localLength⟩
    · cases impossible
    · cases impossible
  have valid := evaluate_normal_while_invariant_by_control inputBlobCondition inputBlobStep invariant
    (by rintro current ⟨i,localIndex,localPointer,localLength⟩; exact ⟨i,localIndex,localPointer,localLength⟩)
    step (fun current => ⟨(evaluate_inputBlob_step_control current).1,(evaluate_inputBlob_step_control current).2.1⟩)
    state post ⟨index,atIndex,atPointer,atLength⟩ run
  obtain ⟨_,_,p,len⟩ := valid
  exact ⟨p,len⟩

/-- A returned copy suffix reports precisely its original pointer and
length. Copying input never changes the allocator or any other global. -/
theorem inputBlob_copy_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (run : evaluateHOLFiniteState state (inputBlobAt 4) = (some (.returned value),post)) :
    value = .rStruct [.val (.word pointer),.val (.word length)] ∧ post.globals = state.globals := by
  have globals : post.globals = state.globals := by
    apply HolFiniteMapExact.ext
    funext key
    have frame := evaluate_avoidsGlobalAssignmentWithSharedLoad key (inputBlobAt 4) (by
      rw [source_inputBlob_stages.2.2.2.2.1,source_inputBlob_stages.2.2.2.2.2.1,
        source_inputBlob_stages.2.2.2.2.2.2.1,source_inputBlob_stages.2.2.2.2.2.2.2]
      rfl) state
    rw [run] at frame
    exact frame
  refine ⟨?_,globals⟩
  rw [source_inputBlob_stages.2.2.2.2.1] at run
  obtain ⟨i,one,initI,runI,_⟩ := evaluate_dec_returned_scope state post (ofString "i") .one (.const 0) _ value run
  have eqI : i = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using initI.symm
  subst i
  rw [source_inputBlob_stages.2.2.2.2.2.1] at runI
  obtain ⟨w,two,initW,runW,_⟩ := evaluate_dec_returned_scope _ one (ofString "w") .one (.const 0) _ value runI
  have eqW : w = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using initW.symm
  subst w
  let ready := setVarHOLFinite (ofString "w") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
  have p : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atPointer,
      show ofString "w" ≠ ofString "p" by decide,show ofString "i" ≠ ofString "p" by decide]
  have len : ready.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atLength,
      show ofString "w" ≠ ofString "len" by decide,show ofString "i" ≠ ofString "len" by decide]
  have index : ready.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "w" ≠ ofString "i" by decide]
  rw [source_inputBlob_stages.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780] at runW
  cases loopRun : evaluateHOLFiniteState ready inputBlobLoop with
  | mk result next =>
    rw [loopRun] at runW
    cases result with
    | some result =>
      have impossible := evaluate_inputBlob_loop_no_return ready value
      rw [loopRun] at impossible
      exact (impossible (Prod.mk.inj runW).1).elim
    | none =>
      dsimp only at runW
      have kept := inputBlob_loop_normal_bindings ready next pointer length 0 p len index loopRun
      rw [source_inputBlob_stages.2.2.2.2.2.2.2] at runW
      have actual : evaluateHOLFiniteState next
          (.return (.rstruct [.var .local (ofString "p"),.var .local (ofString "len")])) =
          (some (.returned (.rStruct [.val (.word pointer),.val (.word length)])),emptyLocalsHOLFinite next) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,kept.1,kept.2,shapeOfHOLExact]
      rw [actual] at runW
      exact (PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj runW).1)).symm

#print axioms inputBlob_loop_normal_bindings
#print axioms inputBlob_copy_returned
end InitECandidate.Runtime
