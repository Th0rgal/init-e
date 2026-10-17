import InitECandidate.Runtime.JournalSetSource32
import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The guarded journal index names a complete, aligned record within its
allocation, with no wraparound in the source word arithmetic. -/
theorem journal_record_geometry32 (journal count capacity : BitVec 64)
    (inside : count.toNat < capacity.toNat)
    (bounded : journal.toNat + capacity.toNat * 32 ≤ 33806089496)
    (aligned : journal.toNat % 8 = 0) :
    (journal + count * 32).toNat = journal.toNat + count.toNat * 32 ∧
    (journal + count * 32).toNat % 8 = 0 ∧
    (journal + count * 32).toNat + 32 ≤ journal.toNat + capacity.toNat * 32 := by
  have address := hashFind_slot_address journal count 32 capacity inside
    (by simpa using bounded) aligned (by decide)
  have product := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt inside)
  have natural := address.1
  change (journal + count * 32).toNat = journal.toNat + count.toNat * 32 at natural
  exact ⟨natural,address.2,by omega⟩

theorem journal_record_domains32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal count capacity : BitVec 64) (inside : count.toNat < capacity.toNat)
    (bounded : journal.toNat + capacity.toNat * 32 ≤ 33806089496) (aligned : journal.toNat % 8 = 0)
    (domain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + capacity.toNat * 32 → state.memaddrs address) :
    ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + count * 32 + BitVec.ofNat 64 offset) := by
  obtain ⟨record,_,extent⟩ := journal_record_geometry32 journal count capacity inside bounded aligned
  intro offset member
  have small : offset < 32 := by simp at member; omega
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have address : (journal + count * 32 + BitVec.ofNat 64 offset).toNat = (journal + count * 32).toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  apply domain <;> omega

/-- Evaluate the exact record-address expression in the original jset body. -/
theorem eval_journal_record_address32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal count : BitVec 64)
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .global (ofString "journal"),.panop .mul [.var .global (ofString "journal_n"),.const 32]]) =
      some (.val (.word (journal + count * 32))) := by
  simp [evalHOLExact,evalListHOLExact,journalGlobal,countGlobal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

/-- The original local record declaration reaches any continuation at the
computed pointer and restores its caller binding on scope exit. -/
theorem evaluate_journal_record_scope32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal count : BitVec 64) (continuation : ProgHOL 64)
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    evaluateHOLFiniteState state
      (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
        .panop .mul [.var .global (ofString "journal_n"),.const 32]]) continuation) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "r") (.val (.word (journal + count * 32))) state) continuation;
        (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (ofString "r",state.locals.lookup (ofString "r")))})) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_journal_record_address32 state journal count journalGlobal countGlobal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (journal + count * 32)))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk]

#print axioms evaluate_journal_record_scope32
#print axioms journal_record_geometry32
#print axioms journal_record_domains32
#print axioms eval_journal_record_address32
end InitECandidate.Runtime
