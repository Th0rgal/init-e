import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def ByteStoreControlFrame {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = state.globals ∧ next.locals = state.locals ∧
    next.code = state.code ∧ next.memaddrs = state.memaddrs

def byteStorePrefix (stores : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  match stores with
  | [] => tail
  | (destination,value) :: rest => .seq (.storeByte destination value) (byteStorePrefix rest tail)

theorem evaluate_storeByte_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (tail : ProgHOL 64) :
    Reaches state (.seq (.storeByte destination value) tail) (ByteStoreControlFrame state) 0 tail := by
  apply reaches_seq
  have facts := evaluate_storeByte_control_frame state destination value
  cases run : evaluateHOLFiniteState state (.storeByte destination value) with
  | mk result next =>
    rw [run] at facts
    dsimp only at facts ⊢
    obtain ⟨control,clock,locals,globals,code,domain,_⟩ := facts
    rcases control with rfl | rfl
    · exact Or.inl ⟨next,⟨globals,locals,code,domain⟩,by omega,by omega,rfl⟩
    · exact Or.inr ⟨.error,rfl,by simp,by dsimp only; omega,
        by dsimp only; omega,by simp⟩

/-- A finite sequence of literal byte stores either reaches its continuation
with all non-memory bindings intact, or rejects, without spending clock. -/
theorem evaluate_byteStore_prefix_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stores : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) :
    Reaches state (byteStorePrefix stores tail) (ByteStoreControlFrame state) 0 tail := by
  induction stores generalizing state with
  | nil => exact Or.inl ⟨state,⟨rfl,rfl,rfl,rfl⟩,by simp,by simp,scoped_refl _⟩
  | cons entry rest ih =>
    obtain ⟨destination,value⟩ := entry
    have firstRun := evaluate_storeByte_reaches state destination value (byteStorePrefix rest tail)
    have composed := reaches_trans state (.seq (.storeByte destination value) (byteStorePrefix rest tail))
      (byteStorePrefix rest tail) tail (ByteStoreControlFrame state) (ByteStoreControlFrame state) 0 0 firstRun
      (by
        intro middle frame
        exact reaches_mono middle (byteStorePrefix rest tail) tail (ByteStoreControlFrame middle)
          (ByteStoreControlFrame state) 0 0 (by omega)
          (by intro next nextFrame; exact ⟨nextFrame.1.trans frame.1,nextFrame.2.1.trans frame.2.1,
            nextFrame.2.2.1.trans frame.2.2.1,nextFrame.2.2.2.trans frame.2.2.2⟩)
          (ih middle))
    exact composed

#print axioms evaluate_storeByte_reaches
#print axioms evaluate_byteStore_prefix_reaches
end InitECandidate.Runtime
