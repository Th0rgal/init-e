import InitECandidate.Runtime.StackWorkCeilingControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl

private theorem decClock_lt {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (positive : s.clock ≠ 0) : (decClock s).clock < s.clock := by
  simp only [decClock]
  omega

theorem stackWork_jump_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F)
    (bounded : CodeSizeState limit s) (ih : CeilingIH limit (.jumpLower r1 r2 dest) s) :
    stackWork (.jumpLower r1 r2 dest) s ≤ workCeiling limit s.clock (sizeOf (.jumpLower r1 r2 dest : HolProg width)) := by
  rw [stackWork]
  split_ifs with zero
  · exact two_le_workCeiling _ _ _
  · cases found : findCode (.inl dest) s.regs s.code with
    | none => exact two_le_workCeiling _ _ _
    | some body =>
      have bodySize := findCode_size s bounded (.inl dest) s.regs body found
      have child := ih body (decClock s) (workRank_clock _ _ _ _ _ (decClock_lt s zero) bodySize)
        bodySize bounded.decClock
      exact workCeiling_one _ _ child

theorem stackWork_tail_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (s : StackSemStateFiniteExact width C F) (bounded : CodeSizeState limit s)
    (ih : CeilingIH limit (.call none dest handler) s) :
    stackWork (.call none dest handler) s ≤ workCeiling limit s.clock (sizeOf (.call none dest handler : HolProg width)) := by
  rw [stackWork]
  split_ifs with zero
  · exact two_le_workCeiling _ _ _
  · cases found : findCode dest s.regs s.code with
    | none => exact two_le_workCeiling _ _ _
    | some body =>
      have bodySize := findCode_size s bounded dest s.regs body found
      have child := ih body (decClock s) (workRank_clock _ _ _ _ _ (decClock_lt s zero) bodySize)
        bodySize bounded.decClock
      exact workCeiling_one _ _ child

theorem stackWork_raw_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit dest : Nat) (s : StackSemStateFiniteExact width C F)
    (bounded : CodeSizeState limit s) (ih : CeilingIH limit (.rawCall dest) s) :
    stackWork (.rawCall dest) s ≤ workCeiling limit s.clock (sizeOf (.rawCall dest : HolProg width)) := by
  rw [stackWork]
  split_ifs with zero
  · exact two_le_workCeiling _ _ _
  · cases found : sptLookup dest s.code with
    | none => exact two_le_workCeiling _ _ _
    | some proc =>
      cases proc
      case seq first body =>
        have sizeBound := bounded.code dest (.seq first body) found
        have childSize := StackSemMeasure.seq_second_size_lt first body
        have bodySize : sizeOf body ≤ limit := by omega
        have child := ih body (decClock s) (workRank_clock _ _ _ _ _ (decClock_lt s zero) bodySize)
          bodySize bounded.decClock
        exact workCeiling_one _ _ child
      all_goals exact two_le_workCeiling _ _ _

theorem stackWork_returning_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (rp : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf (.call (some (rp, link, l1, l2)) dest handler : HolProg width) ≤ limit)
    (bounded : CodeSizeState limit s) (ih : CeilingIH limit (.call (some (rp, link, l1, l2)) dest handler) s) :
    stackWork (.call (some (rp, link, l1, l2)) dest handler) s ≤
      workCeiling limit s.clock (sizeOf (.call (some (rp, link, l1, l2)) dest handler : HolProg width)) := by
  rw [stackWork]
  split_ifs with zero
  · exact two_le_workCeiling _ _ _
  · cases found : findCode dest (s.regs.eraseEq link) s.code with
    | none => exact two_le_workCeiling _ _ _
    | some body =>
      let entry := decClock (Flapjack.StackSemStateOps.setVar link (.loc l1 l2) s)
      let middle := (Flapjack.StackSemControl.fixClock entry (StackSemEvaluate.evaluate (body,entry))).2
      have entryBound : CodeSizeState limit entry := (bounded.setVar link (.loc l1 l2)).decClock
      have entryLt : entry.clock < s.clock := by simp only [entry, decClock, setVar]; omega
      have middleBound : CodeSizeState limit middle := entryBound.evaluated body
      have middleLt : middle.clock < s.clock := by
        have lower := StackSemMeasure.fixClock_clock_le entry (StackSemEvaluate.evaluate (body,entry))
        exact Nat.lt_of_le_of_lt lower entryLt
      have bodySize := findCode_size s bounded dest (s.regs.eraseEq link) body found
      have retSize : sizeOf rp ≤ limit := by
        have small : sizeOf rp < sizeOf (.call (some (rp,link,l1,l2)) dest handler : HolProg width) := by
          simp_wf; omega
        omega
      have cb := ih body entry (workRank_clock _ _ _ _ _ entryLt bodySize) bodySize entryBound
      have rb := ih rp middle (workRank_clock _ _ _ _ _ middleLt retSize) retSize middleBound
      cases handler with
      | none =>
        have combined := workCeiling_three _ _ _ 0 cb rb (Nat.zero_le _)
        simpa only [Nat.add_zero, workCeiling, entry, middle] using combined
      | some desc =>
        rcases desc with ⟨hp,h1,h2⟩
        have handlerSize : sizeOf hp ≤ limit := by
          have small : sizeOf hp < sizeOf (.call (some (rp,link,l1,l2)) dest
              (some (hp,h1,h2)) : HolProg width) := by simp_wf; omega
          omega
        have hb := ih hp middle (workRank_clock _ _ _ _ _ middleLt handlerSize) handlerSize middleBound
        exact workCeiling_three _ _ _ _ cb rb hb

#print axioms stackWork_jump_ceiling
#print axioms stackWork_tail_ceiling
#print axioms stackWork_raw_ceiling
#print axioms stackWork_returning_ceiling
end InitECandidate.Runtime.StackToLab
