import InitECandidate.Runtime.WitnessPhysicalRecord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Remaining child work is read from the actual live record, rather than an
independent abstract counter. Empty and extension records carry no children. -/
def witnessTraversalChildCredit {F : Type} (s : PanSemStateFiniteExact 64 F) (top : BitVec 64) : Nat :=
  if top=0 then 0 else if s.memory (top+8)=.word (2 : BitVec 64) then
    match s.memory (top+32) with
    | .word index => 16-index.toNat
  else 0

theorem witnessTraversalChildCredit_bound {F : Type} (s : PanSemStateFiniteExact 64 F) (top : BitVec 64) :
    witnessTraversalChildCredit s top≤16 := by
  unfold witnessTraversalChildCredit
  split
  · omega
  · split
    · cases cell : s.memory (top+32) with
      | word index => change 16-index.toNat≤16; omega
    · omega

theorem witnessTraversalChildCredit_branch {F : Type} (s : PanSemStateFiniteExact 64 F) (top index : BitVec 64)
    (nonempty : top≠0) (stage : s.memory (top+8)=.word (2 : BitVec 64))
    (cell : s.memory (top+32)=.word index) :
    witnessTraversalChildCredit s top=16-index.toNat := by
  change top≠0#64 at nonempty
  change s.memory (top+8#64)=.word (2#64) at stage
  change s.memory (top+32#64)=.word index at cell
  simp [witnessTraversalChildCredit,nonempty,stage,cell]

theorem witnessTraversalChildCredit_extension {F : Type} (s : PanSemStateFiniteExact 64 F) (top : BitVec 64)
    (stage : s.memory (top+8)=.word (1 : BitVec 64)) : witnessTraversalChildCredit s top=0 := by
  change s.memory (top+8#64)=.word (1#64) at stage
  simp [witnessTraversalChildCredit,stage]

theorem witnessTraversalChildCredit_after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F) (top : BitVec 64)
    (stage : post.memory (top+8)=s.memory (top+8)) (index : post.memory (top+32)=s.memory (top+32)) :
    witnessTraversalChildCredit post top=witnessTraversalChildCredit s top := by
  simp only [witnessTraversalChildCredit,stage,index]

#print axioms witnessTraversalChildCredit_bound
#print axioms witnessTraversalChildCredit_branch
#print axioms witnessTraversalChildCredit_extension
#print axioms witnessTraversalChildCredit_after_frame
end InitECandidate.Runtime
