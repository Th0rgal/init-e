import InitECandidate.Runtime.ComputeJumpdestsBodyFrame
import InitECandidate.Runtime.ComputeJumpdestsGeometry
import InitECandidate.Runtime.NormalWhileInvariantByGuard
import InitECandidate.Runtime.AvoidsLocalFrame
import InitECandidate.Runtime.NoLoopControlStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem compute_jumpdests_active_pc {F : Type} (s : PanSemStateFiniteExact 64 F) (length flag : BitVec 64)
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (guard : evalHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) computeJumpdestsCondition=some (.val (.word flag)))
 (active : flag≠0) : ∃pc : BitVec 64,s.locals.lookup (ofString "pc")=some (.val (.word pc)) ∧pc.toNat<length.toNat := by
 have condition : computeJumpdestsCondition=.cmp .lower (.var .local (ofString "pc")) (.var .local (ofString "n")) := rfl
 rw [condition] at guard
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) _=_ at guard
 simp only [evalHOLExact,atLength] at guard
 cases atPc : s.locals.lookup (ofString "pc") with
 | none=>simp [atPc] at guard
 | some parsed=>
  cases parsed with
  | rStruct values=>simp [atPc] at guard
  | nStruct name values=>simp [atPc] at guard
  | val value=>
   cases value with
   | word pc=>
    refine ⟨pc,rfl,?_⟩
    by_contra denied
    have notLess : ¬pc.toNat<length.toNat := denied
    have flagZero : flag=0 := by
     simpa [atPc,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,notLess] using guard.symm
    exact active flagZero

/-- Normal completion of the real bitmap scan preserves every word at or
above its original scratch frontier. No code-byte readability, room, or
assumed iteration execution is required. -/
theorem compute_jumpdests_loop_upper_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (bitmap length watched : BitVec 64) (frontier : Nat)
 (atBitmap : s.locals.lookup (ofString "bm")=some (.val (.word bitmap)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (small : length.toNat≤134217712)
 (extent : bitmap.toNat+(computeJumpdestsBitmapSize length).toNat≤frontier)
 (cap : frontier≤33806089496) (above : frontier≤watched.toNat)
 (run : evaluateHOLFiniteState s (.while computeJumpdestsCondition computeJumpdestsLoopBody)=(none,post)) :
 post.memory watched=s.memory watched := by
 let invariant:=fun state : PanSemStateFiniteExact 64 F=>
  state.locals.lookup (ofString "bm")=some (.val (.word bitmap)) ∧
  state.locals.lookup (ofString "n")=some (.val (.word length)) ∧state.memory watched=s.memory watched
 have initial : invariant s:=⟨atBitmap,atLength,rfl⟩
 have step : ∀state next flag,invariant state→
  evalHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) computeJumpdestsCondition=some (.val (.word flag))→flag≠0→
  evaluateHOLFiniteState (decClockHOLFinite state) computeJumpdestsLoopBody=(none,next)→invariant next := by
  intro state next flag valid guard active normal
  obtain ⟨pc,atPc,before⟩:=compute_jumpdests_active_pc state length flag valid.2.1 guard active
  have bounded:=compute_jumpdests_bitmap_cell_before_frontier bitmap length pc frontier small before extent cap
  have separate : watched≠bitmap+(pc>>> (6 : Nat))*8 := by
   intro equal
   have eq:=congrArg BitVec.toNat equal
   omega
  have framed:=compute_jumpdests_body_word_frame (decClockHOLFinite state) bitmap pc watched valid.1 atPc separate
  rw [normal] at framed
  have bitmapKept:=evaluate_avoidsLocal_flowing (ofString "bm") computeJumpdestsLoopBody (by decide_cbv)
   (decClockHOLFinite state) (by rw [normal];exact Or.inl rfl)
  have lengthKept:=evaluate_avoidsLocal_flowing (ofString "n") computeJumpdestsLoopBody (by decide_cbv)
   (decClockHOLFinite state) (by rw [normal];exact Or.inl rfl)
  rw [normal] at bitmapKept lengthKept
  exact ⟨bitmapKept.trans valid.1,lengthKept.trans valid.2.1,framed.trans valid.2.2⟩
 have final:=evaluate_normal_while_invariant_by_guard computeJumpdestsCondition computeJumpdestsLoopBody invariant step
  (fun current=>evaluate_noLoopControlStores computeJumpdestsLoopBody (by decide_cbv) current) s post initial run
 exact final.2.2
#print axioms compute_jumpdests_active_pc
#print axioms compute_jumpdests_loop_upper_frame
end InitECandidate.Runtime
