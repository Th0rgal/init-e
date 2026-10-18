import InitECandidate.Runtime.InitializerByteCounterLoop
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def InitializerCounterFinished {F : Type} (state : PanSemStateFiniteExact 64 F)
    (limit : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = state.globals ∧ next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
    next.locals.lookup (ofString "i") = some (.val (.word limit))

/-- The actual local counter declaration and loop reach their continuation,
or terminate on a failed byte store, within the literal iteration count. -/
theorem evaluate_initializer_counter_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (limit : BitVec 64) (destination value : ExpHOL 64) (tail : ProgHOL 64)
    (smallLimit : limit.toNat < 2^63) (budget : limit.toNat ≤ state.clock) :
    Reaches state (.dec (ofString "i") .one (.const 0)
      (.seq (initializerByteCounterLoop limit destination value) tail))
      (InitializerCounterFinished state limit) limit.toNat tail := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,noReturn⟩ :=
    evaluate_initializer_byte_counter_loop entered destination value 0 limit initial smallLimit (by simp)
      (by change limit.toNat - 0 ≤ state.clock; omega)
  have spent : entered.clock ≤ post.clock + limit.toNat := by
    change entered.clock ≤ post.clock + (limit.toNat - 0) at cost
    simpa only [Nat.sub_zero] using cost
  have metadata := evaluateHOLFiniteState_metadata entered (initializerByteCounterLoop limit destination value)
  rw [run] at metadata
  dsimp only at metadata
  have globals : post.globals = state.globals := by
    apply HolFiniteMapExact.ext
    funext key
    have retained := evaluate_avoidsGlobalAssignment key (initializerByteCounterLoop limit destination value) (by rfl) entered
    rw [run] at retained
    exact retained
  have loopReach : Reaches entered (.seq (initializerByteCounterLoop limit destination value) tail)
      (InitializerCounterFinished state limit) limit.toNat tail := by
    apply reaches_seq
    cases result with
    | none => exact Or.inl ⟨post,⟨globals,metadata.1,metadata.2.1,done rfl⟩,spent,remaining,run⟩
    | some result =>
      right
      refine ⟨result,by rw [run],?_,?_,?_,?_⟩
      · intro finalValue equal
        exact noReturn finalValue (congrArg some equal)
      · rw [run]
        exact spent
      · rw [run]
        exact remaining
      · intro _ equal
        exact noTimeout (congrArg some equal)
  have declaration := reaches_dec state (ofString "i") (.const 0)
    (.seq (initializerByteCounterLoop limit destination value) tail) (fun current => current = entered)
    (by
      intro v evaluated
      have equal : v = .val (.word 0) := by simpa [evalHOLExact] using evaluated.symm
      subst v
      exact ⟨0,rfl,rfl⟩)
  have composed := reaches_trans state
    (.dec (ofString "i") .one (.const 0) (.seq (initializerByteCounterLoop limit destination value) tail))
    (.seq (initializerByteCounterLoop limit destination value) tail) tail
    (fun current => current = entered) (InitializerCounterFinished state limit) 0 limit.toNat declaration
    (by intro current equal; subst current; exact loopReach)
  simpa only [Nat.zero_add] using composed

#print axioms evaluate_initializer_counter_reaches
end InitECandidate.Runtime
