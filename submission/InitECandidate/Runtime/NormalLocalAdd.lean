import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def NormalLocalAdd (key : MlS) (amount : BitVec 64) (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (index : BitVec 64),
    state.locals.lookup key = some (.val (.word index)) →
    evaluateHOLFiniteState state program = (none,post) →
    post.locals.lookup key = some (.val (.word (index + amount)))

theorem normalLocalAdd_assign (key : MlS) (amount : BitVec 64) :
    NormalLocalAdd key amount (.assign .local key (.op .add [.var .local key,.const amount])) := by
  intro F state post index binding run
  have actual := evaluate_local_word_assignment state key (.op .add [.var .local key,.const amount])
    index (index + amount) binding
    (by simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord])
  have equal := congrArg Prod.snd (run.symm.trans actual)
  dsimp only at equal
  rw [equal]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem normalLocalAdd_seq (key : MlS) (amount : BitVec 64) (first second : ProgHOL 64)
    (frame : straightLocalFrame key first = true) (tail : NormalLocalAdd key amount second) :
    NormalLocalAdd key amount (.seq first second) := by
  intro F state post index binding run
  have preserved := evaluate_straight_local_frame key first frame state
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [firstRun] at run preserved
    cases result with
    | none => exact tail middle post index (preserved.trans binding) run
    | some result => cases run

theorem normalLocalAdd_dec (key name : MlS) (amount : BitVec 64) (shape : ShapeHOL)
    (initializer : ExpHOL 64) (body : ProgHOL 64) (different : name ≠ key)
    (child : NormalLocalAdd key amount body) : NormalLocalAdd key amount (.dec name shape initializer body) := by
  intro F state post index binding run
  obtain ⟨value,output,_,bodyRun,scope⟩ := evaluate_dec_normal_scope state post name shape initializer body run
  have entered : (setVarHOLFinite name value state).locals.lookup key = some (.val (.word index)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different] using binding
  have advanced := child _ output index entered bodyRun
  rw [scope]
  change (HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)).lookup key = _
  rw [restore_other_local _ name key _ (Ne.symm different)]
  exact advanced

#print axioms normalLocalAdd_dec
#print axioms normalLocalAdd_seq
#print axioms normalLocalAdd_assign
end InitECandidate.Runtime
