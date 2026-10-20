import InitECandidate.Runtime.GuestCostWorkScore
import InitECandidate.Runtime.LoadOneWord
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

/-- The four-word combined shape used by the guest stack and u256 values. -/
def comb4Shape : ShapeHOL := .comb [.one, .one, .one, .one]

theorem comb4Shape_size : sizeOfShapeWithContextHOL ([] : StructContextHOLM) comb4Shape = 4 := by
  simp [comb4Shape, sizeOfShapeWithContextHOL, sizeOfShapeHOL, sizeOfShapesHOL]

/-- A four-word structured load reads the four consecutive word cells starting at
its address. This is the reusable piece shared by `stack_pop` and `u256_add`. -/
theorem eval_load_comb4 (s : PanSemStateFiniteExact 64 F) (address : ExpHOL 64)
    (a w0 w1 w2 w3 : BitVec 64)
    (hAddress : expressionValue s address = some (.val (.word a)))
    (d0 : s.memaddrs a) (d1 : s.memaddrs (a + 8)) (d2 : s.memaddrs (a + 16))
    (d3 : s.memaddrs (a + 24))
    (m0 : s.memory a = .word w0) (m1 : s.memory (a + 8) = .word w1)
    (m2 : s.memory (a + 16) = .word w2) (m3 : s.memory (a + 24) = .word w3) :
    expressionValue s (.load comb4Shape address) =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
  classical
  have d1' : s.memaddrs (a + 8#64) := by simpa using d1
  have h2 : a + 8#64 + 8#64 = a + 16#64 := by
    rw [BitVec.add_assoc]; congr 1
  have h3 : a + 8#64 + 8#64 + 8#64 = a + 24#64 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1
  have d2' : s.memaddrs (a + 8#64 + 8#64) := by rw [h2]; exact d2
  have d3' : s.memaddrs (a + 8#64 + 8#64 + 8#64) := by rw [h3]; exact d3
  have m0' : s.memory a = .word w0 := m0
  have m1' : s.memory (a + 8#64) = .word w1 := by simpa using m1
  have m2' : s.memory (a + 8#64 + 8#64) = .word w2 := by rw [h2]; exact m2
  have m3' : s.memory (a + 8#64 + 8#64 + 8#64) = .word w3 := by rw [h3]; exact m3
  have d0' : s.memaddrs a := d0
  unfold expressionValue at hAddress ⊢
  rw [evalHOLExact]
  simp only [hAddress]
  simp [comb4Shape, memLoadHOLExact, memLoadsHOLExact, bytesInWordHOL,
    sizeOfShapeWithContextHOL, sizeOfShapeHOL, sizeOfShapesHOL,
    d0', d1', d2', d3', m0', m1', m2', m3']

#print axioms comb4Shape_size
#print axioms eval_load_comb4
end InitECandidate.Runtime.FineCost
