import InitECandidate.Proofs.BackendStages.Native
namespace InitECandidate.Runtime.FineCost
open Flapjack InitECandidate.Proofs.BackendStages InitECandidate.Proofs.BackendStages.Native
open Flapjack.Compiler.Backend.Parmove

/-! Certified move table of the pinned allocated Word program (`programs0`,
the input of `WordToStack`). After SSA and register allocation, the moves the
allocator kept (`ssa_cc_trans`'s `stackMov`, `moveArgs`, `retMov`, return and
merge moves, renamed by the colouring) are `.move` nodes of the fixed program.
`WordToStack` schedules a move on physical registers `(dst / 2, src / 2)` with
`parmove`; every emitted move costs at most 12. The table certifies, by
evaluation on the fixed program:

* every `.move` node schedules at most `allocMovePrice` / 12 moves, where
  `allocMovePrice` counts only physical non-self pairs (12 for one, 24 each
  otherwise), so coalesced and self moves are free and cycles are covered;
* at every call site, the move run before the call plus the larger of the moves
  of its return continuation and the leading and trailing moves of its exception
  handler is at most `48 * cutset + 24 * arguments + 24 * returns`. -/

/-- Physical registers of a move's pairs, as `WordToStack` schedules them. -/
def physPairs (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.map (fun p => (p.1 / 2, p.2 / 2))

/-- Price of an allocated move: its physical non-self pairs, 12 for a single
pair and 24 per pair otherwise. -/
def allocMovePrice (pairs : List (Nat × Nat)) : Nat :=
  let n := ((physPairs pairs).filter (fun p => p.1 != p.2)).length
  if n ≤ 1 then 12 * n else 24 * n

/-- `parmove`'s scheduler with explicit fuel: structural, so the kernel
evaluates it on the fixed lists. -/
def pmovFuel : Nat → State Nat → Option (State Nat)
  | 0, _ => none
  | fuel + 1, state =>
    if state.1 = [] ∧ state.2.1 = [] then some state else pmovFuel fuel (fstep state)

theorem pmovFuel_sound : ∀ (fuel : Nat) (state result : State Nat),
    pmovFuel fuel state = some result → pmov state = result
  | 0, _, _, h => by simp [pmovFuel] at h
  | fuel + 1, state, result, h => by
    rw [pmov]
    simp only [pmovFuel] at h
    split at h
    · rename_i finished
      rw [dif_pos finished]
      exact Option.some.inj h
    · rename_i finished
      rw [dif_neg finished]
      exact pmovFuel_sound fuel _ _ h

/-- Initial scheduler state of a move node. -/
def scheduleStart (pairs : List (Nat × Nat)) : State Nat :=
  ((physPairs pairs).map (fun move => (some move.1, some move.2)), [], [])

/-- A move node's scheduled moves are paid by its price (fuel `16 * (n + 1)`). -/
def moveOk (pairs : List (Nat × Nat)) : Bool :=
  match pmovFuel (16 * (pairs.length + 1)) (scheduleStart pairs) with
  | some result => 12 * result.2.2.length ≤ allocMovePrice pairs
  | none => false

theorem moveOk_sound {pairs : List (Nat × Nat)} (ok : moveOk pairs = true) :
    12 * (parmove (physPairs pairs)).length ≤ allocMovePrice pairs := by
  unfold moveOk at ok
  split at ok
  · rename_i result run
    have same := pmovFuel_sound _ _ _ run
    simp only [parmove, List.length_reverse]
    unfold scheduleStart at same
    rw [same]
    simpa using ok
  · cases ok

/-- All move costs of a straight-line program. -/
def allMoves : WordLangProgHOL (BitVec 64) → Nat
  | .seq a b => allMoves a + allMoves b
  | .move _ pairs => allocMovePrice pairs
  | _ => 0

/-- Moves of the leading run of moves and ticks; the flag says whether the whole
program is such a run. -/
def leadingMoves : WordLangProgHOL (BitVec 64) → Nat × Bool
  | .seq a b =>
    let (la, fa) := leadingMoves a
    if fa then let (lb, fb) := leadingMoves b; (la + lb, fb) else (la, false)
  | .move _ pairs => (allocMovePrice pairs, true)
  | .tick | .skip => (0, true)
  | _ => (0, false)

/-- Moves of the trailing run of moves and ticks. -/
def trailingMoves : WordLangProgHOL (BitVec 64) → Nat × Bool
  | .seq a b =>
    let (tb, fb) := trailingMoves b
    if fb then let (ta, fa) := trailingMoves a; (ta + tb, fa) else (tb, false)
  | .move _ pairs => (allocMovePrice pairs, true)
  | .tick | .skip => (0, true)
  | _ => (0, false)

/-- Certified move bound of a call site. -/
def siteBound (cut args rets : Nat) : Nat := 48 * cut + 24 * args + 24 * rets

/-- Return-continuation and handler moves of a call node. -/
def callAfterMoves : WordLangProgHOL (BitVec 64) → Nat
  | .call rets _ _ h =>
    max (match rets with | some (_, _, k, _, _) => allMoves k | none => 0)
      (match h with | some (_, hp, _, _) => (leadingMoves hp).1 + (trailingMoves hp).1 | none => 0)
  | _ => 0

/-- Cutset size of a call node. -/
def callCut : WordLangProgHOL (BitVec 64) → Nat
  | .call (some (_, c, _, _, _)) _ _ _ => sptSize c.1
  | _ => 0

/-- Returned values of a call node. -/
def callRets : WordLangProgHOL (BitVec 64) → Nat
  | .call (some (r, _, _, _, _)) _ _ _ => r.length
  | _ => 0

/-- The table check, given the moves running into the program; returns whether
every move node and call site is paid, and the moves running out of it. A call
site's moves are the run before it plus the larger of its return continuation's
moves and its handler's leading and trailing runs. Written as one forced pass so
the kernel evaluates deep sequences. -/
def goSeq : Nat → WordLangProgHOL (BitVec 64) → Bool × Nat
  | before, .seq a b =>
    match goSeq before a with
    | (true, t) => goSeq t b
    | (false, _) => (false, 0)
  | before, .move _ pairs => (moveOk pairs, before + allocMovePrice pairs)
  | before, .tick => (true, before)
  | before, .skip => (true, before)
  | before, .call rets target args h =>
    let node := WordLangProgHOL.call rets target args h
    (decide (before + callAfterMoves node ≤ siteBound (callCut node) args.length (callRets node)) &&
      (match rets with | some (_, _, k, _, _) => (goSeq 0 k).1 | none => true) &&
      (match h with | some (_, hp, _, _) => (goSeq 0 hp).1 | none => true), 0)
  | _, .ite _ _ _ a b => ((goSeq 0 a).1 && (goSeq 0 b).1, 0)
  | _, .loop _ b _ => ((goSeq 0 b).1, 0)
  | _, .mustTerminate b => ((goSeq 0 b).1, 0)
  | _, _ => (true, 0)

theorem goSeq_seq {before : Nat} {a b : WordLangProgHOL (BitVec 64)}
    (ok : (goSeq before (.seq a b)).1 = true) :
    (goSeq before a).1 = true ∧ (goSeq (goSeq before a).2 b).1 = true := by
  simp only [goSeq] at ok
  split at ok
  · rename_i t h
    rw [h]
    exact ⟨rfl, ok⟩
  · cases ok

theorem goSeq_move {before pri} {pairs : List (Nat × Nat)}
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    12 * (parmove (physPairs pairs)).length ≤ allocMovePrice pairs :=
  moveOk_sound ok

/-- A call site's moves are within its bound. -/
theorem goSeq_call {before rets target args h}
    (ok : (goSeq before (.call rets target args h)).1 = true) :
    before + callAfterMoves (.call rets target args h) ≤
      siteBound (callCut (.call rets target args h)) args.length (callRets (.call rets target args h)) := by
  unfold goSeq at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  exact ok.1.1

/-- The return continuation of a call site is paid. -/
theorem goSeq_call_return {before r c k l1 l2 target args h}
    (ok : (goSeq before (.call (some (r, c, k, l1, l2)) target args h)).1 = true) :
    (goSeq 0 k).1 = true := by
  unfold goSeq at ok
  simp only [Bool.and_eq_true] at ok
  exact ok.1.2

/-- The exception handler of a call site is paid. -/
theorem goSeq_call_handler {before rets target args n hp l1 l2}
    (ok : (goSeq before (.call rets target args (some (n, hp, l1, l2)))).1 = true) :
    (goSeq 0 hp).1 = true := by
  unfold goSeq at ok
  simp only [Bool.and_eq_true] at ok
  exact ok.2

/-- A function of the fixed program meets the move and call-site table. -/
def entryOk (entry : Nat × Nat × WordLangProgHOL (BitVec 64)) : Bool := (goSeq 0 entry.2.2).1

theorem table_Chunk880_889 : Chunk880_889.programs.all entryOk = true := by decide +kernel
theorem table_Chunk864_879 : Chunk864_879.programs.all entryOk = true := by decide +kernel
theorem table_Chunk848_863 : Chunk848_863.programs.all entryOk = true := by decide +kernel
theorem table_Chunk832_847 : Chunk832_847.programs.all entryOk = true := by decide +kernel
theorem table_Chunk816_831 : Chunk816_831.programs.all entryOk = true := by decide +kernel
theorem table_Chunk800_815 : Chunk800_815.programs.all entryOk = true := by decide +kernel
theorem table_Chunk784_799 : Chunk784_799.programs.all entryOk = true := by decide +kernel
theorem table_Chunk768_783 : Chunk768_783.programs.all entryOk = true := by decide +kernel
theorem table_Chunk752_767 : Chunk752_767.programs.all entryOk = true := by decide +kernel
theorem table_Chunk736_751 : Chunk736_751.programs.all entryOk = true := by decide +kernel
theorem table_Chunk720_735 : Chunk720_735.programs.all entryOk = true := by decide +kernel
theorem table_Chunk704_719 : Chunk704_719.programs.all entryOk = true := by decide +kernel
theorem table_Chunk688_703 : Chunk688_703.programs.all entryOk = true := by decide +kernel
theorem table_Chunk672_687 : Chunk672_687.programs.all entryOk = true := by decide +kernel
theorem table_Chunk656_671 : Chunk656_671.programs.all entryOk = true := by decide +kernel
theorem table_Chunk640_655 : Chunk640_655.programs.all entryOk = true := by decide +kernel
theorem table_Chunk624_639 : Chunk624_639.programs.all entryOk = true := by decide +kernel
theorem table_Chunk608_623 : Chunk608_623.programs.all entryOk = true := by decide +kernel
theorem table_Chunk592_607 : Chunk592_607.programs.all entryOk = true := by decide +kernel
theorem table_Chunk576_591 : Chunk576_591.programs.all entryOk = true := by decide +kernel
theorem table_Chunk560_575 : Chunk560_575.programs.all entryOk = true := by decide +kernel
theorem table_Chunk544_559 : Chunk544_559.programs.all entryOk = true := by decide +kernel
theorem table_Chunk528_543 : Chunk528_543.programs.all entryOk = true := by decide +kernel
theorem table_Chunk512_527 : Chunk512_527.programs.all entryOk = true := by decide +kernel
theorem table_Chunk496_511 : Chunk496_511.programs.all entryOk = true := by decide +kernel
theorem table_Chunk480_495 : Chunk480_495.programs.all entryOk = true := by decide +kernel
theorem table_Chunk464_479 : Chunk464_479.programs.all entryOk = true := by decide +kernel
theorem table_Chunk448_463 : Chunk448_463.programs.all entryOk = true := by decide +kernel
theorem table_Chunk432_447 : Chunk432_447.programs.all entryOk = true := by decide +kernel
theorem table_Chunk416_431 : Chunk416_431.programs.all entryOk = true := by decide +kernel
theorem table_Chunk400_415 : Chunk400_415.programs.all entryOk = true := by decide +kernel
theorem table_Chunk384_399 : Chunk384_399.programs.all entryOk = true := by decide +kernel
theorem table_Chunk368_383 : Chunk368_383.programs.all entryOk = true := by decide +kernel
theorem table_Chunk352_367 : Chunk352_367.programs.all entryOk = true := by decide +kernel
theorem table_Chunk336_351 : Chunk336_351.programs.all entryOk = true := by decide +kernel
theorem table_Chunk320_335 : Chunk320_335.programs.all entryOk = true := by decide +kernel
theorem table_Chunk304_319 : Chunk304_319.programs.all entryOk = true := by decide +kernel
theorem table_Chunk288_303 : Chunk288_303.programs.all entryOk = true := by decide +kernel
theorem table_Chunk272_287 : Chunk272_287.programs.all entryOk = true := by decide +kernel
theorem table_Chunk256_271 : Chunk256_271.programs.all entryOk = true := by decide +kernel
theorem table_Chunk240_255 : Chunk240_255.programs.all entryOk = true := by decide +kernel
theorem table_Chunk224_239 : Chunk224_239.programs.all entryOk = true := by decide +kernel
theorem table_Chunk208_223 : Chunk208_223.programs.all entryOk = true := by decide +kernel
theorem table_Chunk192_207 : Chunk192_207.programs.all entryOk = true := by decide +kernel
theorem table_Chunk176_191 : Chunk176_191.programs.all entryOk = true := by decide +kernel
theorem table_Chunk160_175 : Chunk160_175.programs.all entryOk = true := by decide +kernel
theorem table_Chunk144_159 : Chunk144_159.programs.all entryOk = true := by decide +kernel
theorem table_Chunk128_143 : Chunk128_143.programs.all entryOk = true := by decide +kernel
theorem table_Chunk112_127 : Chunk112_127.programs.all entryOk = true := by decide +kernel
theorem table_Chunk96_111 : Chunk96_111.programs.all entryOk = true := by decide +kernel
theorem table_Chunk80_95 : Chunk80_95.programs.all entryOk = true := by decide +kernel
theorem table_Chunk64_79 : Chunk64_79.programs.all entryOk = true := by decide +kernel

theorem table_programs52 : programs52.all entryOk = true := rfl
theorem table_programs51 : programs51.all entryOk = true := by
  rw [programs51, List.all_append, table_Chunk880_889, table_programs52]; rfl
theorem table_programs50 : programs50.all entryOk = true := by
  rw [programs50, List.all_append, table_Chunk864_879, table_programs51]; rfl
theorem table_programs49 : programs49.all entryOk = true := by
  rw [programs49, List.all_append, table_Chunk848_863, table_programs50]; rfl
theorem table_programs48 : programs48.all entryOk = true := by
  rw [programs48, List.all_append, table_Chunk832_847, table_programs49]; rfl
theorem table_programs47 : programs47.all entryOk = true := by
  rw [programs47, List.all_append, table_Chunk816_831, table_programs48]; rfl
theorem table_programs46 : programs46.all entryOk = true := by
  rw [programs46, List.all_append, table_Chunk800_815, table_programs47]; rfl
theorem table_programs45 : programs45.all entryOk = true := by
  rw [programs45, List.all_append, table_Chunk784_799, table_programs46]; rfl
theorem table_programs44 : programs44.all entryOk = true := by
  rw [programs44, List.all_append, table_Chunk768_783, table_programs45]; rfl
theorem table_programs43 : programs43.all entryOk = true := by
  rw [programs43, List.all_append, table_Chunk752_767, table_programs44]; rfl
theorem table_programs42 : programs42.all entryOk = true := by
  rw [programs42, List.all_append, table_Chunk736_751, table_programs43]; rfl
theorem table_programs41 : programs41.all entryOk = true := by
  rw [programs41, List.all_append, table_Chunk720_735, table_programs42]; rfl
theorem table_programs40 : programs40.all entryOk = true := by
  rw [programs40, List.all_append, table_Chunk704_719, table_programs41]; rfl
theorem table_programs39 : programs39.all entryOk = true := by
  rw [programs39, List.all_append, table_Chunk688_703, table_programs40]; rfl
theorem table_programs38 : programs38.all entryOk = true := by
  rw [programs38, List.all_append, table_Chunk672_687, table_programs39]; rfl
theorem table_programs37 : programs37.all entryOk = true := by
  rw [programs37, List.all_append, table_Chunk656_671, table_programs38]; rfl
theorem table_programs36 : programs36.all entryOk = true := by
  rw [programs36, List.all_append, table_Chunk640_655, table_programs37]; rfl
theorem table_programs35 : programs35.all entryOk = true := by
  rw [programs35, List.all_append, table_Chunk624_639, table_programs36]; rfl
theorem table_programs34 : programs34.all entryOk = true := by
  rw [programs34, List.all_append, table_Chunk608_623, table_programs35]; rfl
theorem table_programs33 : programs33.all entryOk = true := by
  rw [programs33, List.all_append, table_Chunk592_607, table_programs34]; rfl
theorem table_programs32 : programs32.all entryOk = true := by
  rw [programs32, List.all_append, table_Chunk576_591, table_programs33]; rfl
theorem table_programs31 : programs31.all entryOk = true := by
  rw [programs31, List.all_append, table_Chunk560_575, table_programs32]; rfl
theorem table_programs30 : programs30.all entryOk = true := by
  rw [programs30, List.all_append, table_Chunk544_559, table_programs31]; rfl
theorem table_programs29 : programs29.all entryOk = true := by
  rw [programs29, List.all_append, table_Chunk528_543, table_programs30]; rfl
theorem table_programs28 : programs28.all entryOk = true := by
  rw [programs28, List.all_append, table_Chunk512_527, table_programs29]; rfl
theorem table_programs27 : programs27.all entryOk = true := by
  rw [programs27, List.all_append, table_Chunk496_511, table_programs28]; rfl
theorem table_programs26 : programs26.all entryOk = true := by
  rw [programs26, List.all_append, table_Chunk480_495, table_programs27]; rfl
theorem table_programs25 : programs25.all entryOk = true := by
  rw [programs25, List.all_append, table_Chunk464_479, table_programs26]; rfl
theorem table_programs24 : programs24.all entryOk = true := by
  rw [programs24, List.all_append, table_Chunk448_463, table_programs25]; rfl
theorem table_programs23 : programs23.all entryOk = true := by
  rw [programs23, List.all_append, table_Chunk432_447, table_programs24]; rfl
theorem table_programs22 : programs22.all entryOk = true := by
  rw [programs22, List.all_append, table_Chunk416_431, table_programs23]; rfl
theorem table_programs21 : programs21.all entryOk = true := by
  rw [programs21, List.all_append, table_Chunk400_415, table_programs22]; rfl
theorem table_programs20 : programs20.all entryOk = true := by
  rw [programs20, List.all_append, table_Chunk384_399, table_programs21]; rfl
theorem table_programs19 : programs19.all entryOk = true := by
  rw [programs19, List.all_append, table_Chunk368_383, table_programs20]; rfl
theorem table_programs18 : programs18.all entryOk = true := by
  rw [programs18, List.all_append, table_Chunk352_367, table_programs19]; rfl
theorem table_programs17 : programs17.all entryOk = true := by
  rw [programs17, List.all_append, table_Chunk336_351, table_programs18]; rfl
theorem table_programs16 : programs16.all entryOk = true := by
  rw [programs16, List.all_append, table_Chunk320_335, table_programs17]; rfl
theorem table_programs15 : programs15.all entryOk = true := by
  rw [programs15, List.all_append, table_Chunk304_319, table_programs16]; rfl
theorem table_programs14 : programs14.all entryOk = true := by
  rw [programs14, List.all_append, table_Chunk288_303, table_programs15]; rfl
theorem table_programs13 : programs13.all entryOk = true := by
  rw [programs13, List.all_append, table_Chunk272_287, table_programs14]; rfl
theorem table_programs12 : programs12.all entryOk = true := by
  rw [programs12, List.all_append, table_Chunk256_271, table_programs13]; rfl
theorem table_programs11 : programs11.all entryOk = true := by
  rw [programs11, List.all_append, table_Chunk240_255, table_programs12]; rfl
theorem table_programs10 : programs10.all entryOk = true := by
  rw [programs10, List.all_append, table_Chunk224_239, table_programs11]; rfl
theorem table_programs9 : programs9.all entryOk = true := by
  rw [programs9, List.all_append, table_Chunk208_223, table_programs10]; rfl
theorem table_programs8 : programs8.all entryOk = true := by
  rw [programs8, List.all_append, table_Chunk192_207, table_programs9]; rfl
theorem table_programs7 : programs7.all entryOk = true := by
  rw [programs7, List.all_append, table_Chunk176_191, table_programs8]; rfl
theorem table_programs6 : programs6.all entryOk = true := by
  rw [programs6, List.all_append, table_Chunk160_175, table_programs7]; rfl
theorem table_programs5 : programs5.all entryOk = true := by
  rw [programs5, List.all_append, table_Chunk144_159, table_programs6]; rfl
theorem table_programs4 : programs4.all entryOk = true := by
  rw [programs4, List.all_append, table_Chunk128_143, table_programs5]; rfl
theorem table_programs3 : programs3.all entryOk = true := by
  rw [programs3, List.all_append, table_Chunk112_127, table_programs4]; rfl
theorem table_programs2 : programs2.all entryOk = true := by
  rw [programs2, List.all_append, table_Chunk96_111, table_programs3]; rfl
theorem table_programs1 : programs1.all entryOk = true := by
  rw [programs1, List.all_append, table_Chunk80_95, table_programs2]; rfl
theorem table_programs0 : programs0.all entryOk = true := by
  rw [programs0, List.all_append, table_Chunk64_79, table_programs1]; rfl

/-- The pinned allocated program meets the move and call-site table. -/
theorem allocMoveTable : programs0.all entryOk = true := table_programs0

theorem allocMoveTable_entry {entry} (mem : entry ∈ programs0) : entryOk entry = true :=
  List.all_eq_true.1 allocMoveTable entry mem

#print axioms goSeq_seq
#print axioms goSeq_move
#print axioms goSeq_call
#print axioms goSeq_call_return
#print axioms goSeq_call_handler
#print axioms allocMoveTable_entry
end InitECandidate.Runtime.FineCost
