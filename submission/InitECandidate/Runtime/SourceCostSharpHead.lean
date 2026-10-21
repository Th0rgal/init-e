import InitECandidate.Runtime.SourceCostSharpLowering
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! A `k`-word structured load re-evaluates only the head of its compiled
address for every further word. This module bounds that head's exact Loop price
syntactically: a record field of a local selects one compiled variable. -/

/-- Every compiled element is a variable or a constant. -/
def CrepSmall (expressions : List (CrepExpHOL 64)) : Prop :=
  ∀ e ∈ expressions, loopNodePrice e ≤ 2

theorem crepSmall_compField (index : Nat) (shapes : List ShapeHOL) (expressions : List (CrepExpHOL 64))
    (small : CrepSmall expressions) : CrepSmall (compFieldHOL index shapes expressions).1 := by
  induction shapes generalizing index expressions with
  | nil => intro e he; simp [compFieldHOL] at he; subst he; simp [loopNodePrice]
  | cons shape shapes ih =>
    rw [compFieldHOL]
    split
    · exact fun e he => small e (List.mem_of_mem_take he)
    · exact ih _ _ (fun e he => small e (List.mem_of_mem_drop he))

/-- Locals and record fields of locals. -/
def localTree : ExpHOL 64 → Bool
  | .var .local _ => true
  | .rfield _ e => localTree e
  | _ => false

theorem localTree_small (context : PanToCrepContextExact 64) :
    ∀ e : ExpHOL 64, localTree e = true → CrepSmall (compileExpExactHOLW context e).1
  | .var .local name, _ => by
    intro x hx
    simp only [compileExpExactHOLW] at hx
    split at hx
    · obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx; simp [loopNodePrice]
    · simp at hx; subst hx; simp [loopNodePrice]
  | .rfield index e, tree => by
    have inner := localTree_small context e (by simpa [localTree] using tree)
    intro x hx
    simp only [compileExpExactHOLW] at hx
    split at hx
    · exact crepSmall_compField _ _ _ inner x hx
    · simp at hx; subst hx; simp [loopNodePrice]
  | .var .global _, tree | .const _, tree | .rstruct _, tree | .nstruct _ _, tree | .nfield _ _, tree
  | .load _ _, tree | .load32 _, tree | .loadByte _, tree | .op _ _, tree | .panop _ _, tree
  | .cmp _ _ _, tree | .shift _ _ _, tree | .baseAddr, tree | .topAddr, tree | .bytesInWord, tree => by
    simp [localTree] at tree

theorem crepHead_small {expressions : List (CrepExpHOL 64)} (small : CrepSmall expressions) :
    crepHead expressions ≤ 2 := by
  cases expressions with
  | nil => simp [crepHead]
  | cons head tail => exact small head (by simp)

#print axioms localTree_small

mutual
  /-- Address grammar with a context-free head price: scalar expressions over
  locals, record fields of locals, constants, `BaseAddr`/`TopAddr`, operators
  and nested loads. -/
  def headAddr : ExpHOL 64 → Bool
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
    | .rfield _ e => localTree e
    | .op _ args | .panop _ args => headAddrList args
    | .cmp _ left right | .shift _ left right => headAddr left && headAddr right
    | .load _ address | .load32 address | .loadByte address => headAddr address
    | _ => false
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def headAddrList : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => headAddr head && headAddrList tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Context-free bound on the Loop price of the compiled head. -/
  def sharpHeadPrice : ExpHOL 64 → Nat
    | .topAddr => 6
    | .op _ args => 2 + sharpHeadListPrice args
    | .panop _ args => 3 + sharpHeadListPrice args
    | .cmp _ left right => 6 + sharpHeadPrice left + sharpHeadPrice right
    | .shift _ left right => sharpHeadPrice left + sharpHeadPrice right
    | .load _ address => sharpHeadPrice address + 1
    | .load32 address | .loadByte address => sharpHeadPrice address + 3
    | _ => 2
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def sharpHeadListPrice : List (ExpHOL 64) → Nat
    | [] => 0
    | head :: tail => sharpHeadPrice head + sharpHeadListPrice tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem sharpHeadPrice_two : ∀ e : ExpHOL 64, 2 ≤ sharpHeadPrice e := by
  refine ExpHOL.rec (motive_1 := fun e => 2 ≤ sharpHeadPrice e) (motive_2 := fun _ => True)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals first | trivial | (simp only [sharpHeadPrice]; omega)

theorem crepHead_loadShape (count : Nat) (address : CrepExpHOL 64) :
    crepHead (loadShapeBytesHOLW 0 count address) ≤ loopNodePrice address + 1 := by
  cases count with
  | zero => simp [loadShapeBytesHOLW, crepHead]
  | succ count => simp [loadShapeBytesHOLW, crepHead, loopNodePrice]

/-- The compiled head of a grammar address costs at most `sharpHeadPrice`. -/
theorem head_bound (context : PanToCrepContextExact 64) :
    ∀ e : ExpHOL 64, headAddr e = true →
      crepHead (compileExpExactHOLW context e).1 ≤ sharpHeadPrice e := by
  refine ExpHOL.rec
    (motive_1 := fun e => headAddr e = true →
      crepHead (compileExpExactHOLW context e).1 ≤ sharpHeadPrice e)
    (motive_2 := fun es => headAddrList es = true → ∀ heads,
      cexpHeads ((compileExpExactHOLWList context es).map Prod.fst) = some heads →
        loopPriceList heads ≤ sharpHeadListPrice es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value _
    simp [compileExpExactHOLW, crepHead, loopNodePrice, sharpHeadPrice]
  · intro kind name _
    have small : CrepSmall (compileExpExactHOLW context (.var kind name)).1 := by
      cases kind
      · exact localTree_small context _ rfl
      · intro x hx; simp [compileExpExactHOLW] at hx; subst hx; simp [loopNodePrice]
    have := crepHead_small small
    cases kind <;> simp only [sharpHeadPrice] <;> omega
  · intro fields _ ready
    simp [headAddr] at ready
  · intro index value _ ready
    simp only [headAddr] at ready
    have := crepHead_small (localTree_small context (.rfield index value) (by simpa [localTree] using ready))
    simp only [sharpHeadPrice]; omega
  · intro name fields _ ready
    simp [headAddr] at ready
  · intro name value _ ready
    simp [headAddr] at ready
  · intro shape address ih ready
    simp only [headAddr] at ready
    have inner := ih ready
    simp only [compileExpExactHOLW]
    split
    · rename_i head tail _ heq
      rw [heq] at inner
      have := crepHead_loadShape (sizeOfShapeHOL shape) head
      simp only [crepHead] at inner
      simp only [sharpHeadPrice]; omega
    · have := sharpHeadPrice_two address
      simp [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro address ih ready
    simp only [headAddr] at ready
    have inner := ih ready
    have := sharpHeadPrice_two address
    simp only [compileExpExactHOLW]
    split
    · rename_i head _ heq
      rw [heq] at inner
      simp only [crepHead, loopNodePrice, sharpHeadPrice] at inner ⊢; omega
    · simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro address ih ready
    simp only [headAddr] at ready
    have inner := ih ready
    have := sharpHeadPrice_two address
    simp only [compileExpExactHOLW]
    split
    · rename_i head _ heq
      rw [heq] at inner
      simp only [crepHead, loopNodePrice, sharpHeadPrice] at inner ⊢; omega
    · simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro operator args ih ready
    simp only [headAddr] at ready
    simp only [compileExpExactHOLW]
    split
    · rename_i heads hh
      have := ih ready heads hh
      simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
    · simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro operator args ih ready
    simp only [headAddr] at ready
    simp only [compileExpExactHOLW]
    split
    · rename_i heads hh
      have := ih ready heads hh
      simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
    · simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro operator left right ihLeft ihRight ready
    simp only [headAddr, Bool.and_eq_true] at ready
    have a := ihLeft ready.1
    have b := ihRight ready.2
    have := sharpHeadPrice_two left
    simp only [compileExpExactHOLW]
    split
    · rename_i l _ _ r _ _ hl hr
      rw [hl] at a; rw [hr] at b
      simp only [crepHead, loopNodePrice, sharpHeadPrice] at a b ⊢; omega
    · simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro operator left right ihLeft ihRight ready
    simp only [headAddr, Bool.and_eq_true] at ready
    have a := ihLeft ready.1
    have b := ihRight ready.2
    have := sharpHeadPrice_two left
    simp only [compileExpExactHOLW]
    split
    · rename_i l _ _ r _ _ hl hr
      rw [hl] at a; rw [hr] at b
      simp only [crepHead, loopNodePrice, sharpHeadPrice] at a b ⊢; omega
    · simp only [crepHead, loopNodePrice, sharpHeadPrice]; omega
  · intro _; simp [compileExpExactHOLW, crepHead, loopNodePrice, sharpHeadPrice]
  · intro _; simp [compileExpExactHOLW, crepHead, loopNodePrice, sharpHeadPrice]
  · intro _; simp [compileExpExactHOLW, crepHead, loopNodePrice, sharpHeadPrice]
  · intro _ heads hh
    simp [compileExpExactHOLWList, cexpHeads] at hh
    subst hh; simp [loopPriceList]
  · intro head tail ihHead ihTail ready heads hh
    simp only [headAddrList, Bool.and_eq_true] at ready
    have a := ihHead ready.1
    simp only [compileExpExactHOLWList, List.map_cons, cexpHeads] at hh
    split at hh
    · simp at hh
    · simp at hh
    · rename_i x _ rest hx hrest
      simp only [Option.some.injEq] at hh
      subst hh
      have b := ihTail ready.2 rest hrest
      rw [hx] at a
      simp only [crepHead] at a
      simp only [loopPriceList, sharpHeadListPrice]; omega
  · trivial
  · intros; trivial
  · intros; trivial

#print axioms head_bound
end InitECandidate.Runtime.FineCost

