import InitECandidate.Runtime.RecordHashSource
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def RecordHashLocals {F : Type} (state : PanSemStateFiniteExact 64 F) (e ch out : BitVec 64) : Prop :=
  state.locals.lookup (ofString "e") = some (.val (.word e)) ∧
  state.locals.lookup (ofString "ch") = some (.val (.word ch)) ∧
  state.locals.lookup (ofString "out") = some (.val (.word out))

def RecordHashBound (program : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (e ch out heap : BitVec 64), RecordHashLocals state e ch out →
    state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) → heap.toNat ≤ 33806089496 →
    state.code = originalRuntimeCode → cost ≤ state.clock → RunBounded state program cost

theorem recordHashAddress_eval {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (base offset : BitVec 64)
    (atLocal : state.locals.lookup name = some (.val (.word base))) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) (recordHashAddress name offset) =
      some (.val (.word (base + offset))) := by
  by_cases zero : offset = (0#64)
  · subst offset
    simp [recordHashAddress,evalHOLExact,atLocal]
  · simp [recordHashAddress,zero,evalHOLExact,evalListHOLExact,atLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem recordHash_finish_bound (count : BitVec 64) (small : count.toNat ≤ 134217712) :
    RecordHashBound (recordHashFinish count) ((merkleBodyCost + 1) + 1) := by
  intro F state e ch out heap locals hh cap code budget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "ch"),.const count,.const count,.var .local (ofString "out")] =
      some [.val (.word ch),.val (.word count),.val (.word count),.val (.word out)] := by
    simp [evalListHOLExact,evalHOLExact,locals.2.1,locals.2.2]
  exact RunBounded.seq (runBounded_merkleize_call state none _ ch count count out heap args small hh cap code (by omega)) budget (by
    intro post normal postCode remaining
    exact RunBounded.ofProg
      (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
      (postCode.trans code) remaining)

theorem recordHash_step_bound (step : RecordHashStep) (small : step.Small) (tail : ProgHOL 64) (cost : Nat)
    (bounded : RecordHashBound tail cost) :
    RecordHashBound (.seq (.call (some (none,none)) step.function step.arguments) tail) (step.cost + cost) := by
  intro F state e ch out heap locals hh cap code budget
  have extend (function : MlS) (arguments : List (ExpHOL 64)) (ticks : Nat)
      (first : RunBounded state (.call (some (none,none)) function arguments) ticks)
      (enough : ticks + cost ≤ state.clock)
      (frame : ∀ post, evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post) →
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))) :
      RunBounded state (.seq (.call (some (none,none)) function arguments) tail) (ticks + cost) := by
    apply runBounded_discard_heap_seq state function arguments tail (ofString "heap_ptr") heap ticks cost first enough frame
    intro post keep heapKept postCode remaining
    exact bounded post e ch out heap ⟨(keep _).trans locals.1,(keep _).trans locals.2.1,(keep _).trans locals.2.2⟩
      heapKept cap (postCode.trans code) remaining
  cases step with
  | vector i n o =>
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (RecordHashStep.vector i n o).arguments =
        some [.val (.word (e + i)),.val (.word n),.val (.word (ch + o))] := by
      simp only [RecordHashStep.arguments,evalListHOLFinite,evalListHOLExact,recordHashAddress_eval state _ e i locals.1,
        recordHashAddress_eval state _ ch o locals.2.1,evalHOLExact]
      <;> rfl
    exact extend _ _ _ (runBounded_htrBytesVector_call state none _ (e+i) n (ch+o) heap args small hh cap code (by exact Nat.le_trans (Nat.le_add_right _ _) budget)) budget
      (fun post normal => htrBytesVector_call_normal_heap state post _ (e+i) n (ch+o) heap args code hh normal)
  | copy i o =>
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        (RecordHashStep.copy i o).arguments =
        some [.val (.word (ch + o)),.val (.word (e + i)),.val (.word (32#64))] := by
      simp only [RecordHashStep.arguments,evalListHOLFinite,evalListHOLExact,recordHashAddress_eval state _ e i locals.1,
        recordHashAddress_eval state _ ch o locals.2.1,evalHOLExact]
      <;> rfl
    exact extend _ _ 16 (evaluate_memcpy_call_bounded state _ (ch+o) (e+i) (32#64) args code (by decide) (by change 16 ≤ state.clock; exact Nat.le_trans (Nat.le_add_right _ _) budget)) budget (by
      intro post normal
      have globals := memcpy_call_globals_frame (RecordHashStep.copy i o).arguments state code
      simp only [RecordHashStep.function] at normal
      rw [normal] at globals
      rw [globals]; exact hh)
  | uint i o =>
    exact extend _ _ 30 (RunBounded.ofProg (ProgBounded.call htrU64At_funBounded _ _) code (by exact Nat.le_trans (Nat.le_add_right _ _) budget)) budget (by
      intro post normal
      have globals := htrU64At_call_globals (RecordHashStep.uint i o).arguments state code
      simp only [RecordHashStep.function] at normal
      rw [normal] at globals
      rw [globals]; exact hh)

theorem recordHash_suffix_bound (steps : List RecordHashStep) (count : BitVec 64)
    (small : ∀ step ∈ steps, step.Small) (countBound : count.toNat ≤ 134217712) :
    RecordHashBound (recordHashSuffix steps count) (recordHashCost steps) := by
  induction steps with
  | nil => exact recordHash_finish_bound count countBound
  | cons step rest ih =>
    exact recordHash_step_bound step (small step (by simp)) _ _
      (ih (fun s mem => small s (by simp [mem])))

#print axioms recordHashAddress_eval
#print axioms recordHash_finish_bound
#print axioms recordHash_step_bound
#print axioms recordHash_suffix_bound
end InitECandidate.Runtime
