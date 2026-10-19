import InitECandidate.Runtime.HashFindLoopReturnedOccupied
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful probe tail returns either the capacity sentinel or an
occupied in-range slot, without assumptions on the query address. -/
theorem hash_find_tail_returned_occupied {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (initial capacity used : BitVec 64) (bits : Nat) (value : ValueHOL 64)
    (power : capacity.toNat = 2 ^ bits)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word initial)))
    (inside : initial.toNat < capacity.toNat)
    (atCapacity : s.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (atUsed : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s hashFindTail = (some (.returned value),post)) :
    ∃ index : BitVec 64, value = .val (.word index) ∧ index.toNat ≤ capacity.toNat ∧
      (index ≠ capacity → hashOccupancyRead s used index ≠ some 0) := by
  unfold hashFindTail at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState s hashFindLoop with
  | mk outcome middle =>
    rw [loopRun] at run
    cases outcome with
    | none =>
      have kept := evaluate_avoidsLocal_flowing (ofString "cap") hashFindLoop (by decide) s
        (by rw [loopRun]; exact Or.inl rfl)
      rw [loopRun] at kept
      simp only at run
      exact ⟨capacity,return_local_word middle post (ofString "cap") capacity value
        (kept.trans atCapacity) run,le_refl _,by intro ne; exact False.elim (ne rfl)⟩
    | some outcome =>
      simp only at run
      obtain ⟨same,_⟩ := Prod.mk.inj run
      have result : outcome = .returned value := Option.some.inj same
      subst outcome
      obtain ⟨index,word,lt,occupied⟩ := hash_find_loop_returned_occupied s middle initial capacity used bits value
        power atIndex inside atCapacity atUsed code loopRun
      exact ⟨index,word,Nat.le_of_lt lt,fun _ => occupied⟩

#print axioms hash_find_tail_returned_occupied
end InitECandidate.Runtime
