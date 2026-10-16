import InitECandidate.Runtime.HashProbeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Follow declarations and skip earlier loop-free statements. -/
def hashDeleteLeadingWhile : ProgHOL 64 → Option (ExpHOL 64 × ProgHOL 64)
  | .while condition body => some (condition,body)
  | .dec _ _ _ body => hashDeleteLeadingWhile body
  | .decCall _ _ _ _ body => hashDeleteLeadingWhile body
  | .seq first rest => (hashDeleteLeadingWhile first).orElse (fun _ => hashDeleteLeadingWhile rest)
  | _ => none

def hashDeleteLoopRest : ProgHOL 64 :=
  match hashDeleteLeadingWhile (sourceFunctionBody Guest.guestFn_htab_del) with
  | some (_, .seq _ (.seq _ rest)) => rest
  | _ => .skip

def hashDeleteEmpty : ExpHOL 64 :=
  .cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0)

def hashDeleteLoopBody : ProgHOL 64 :=
  .seq (hashProbeStep (ofString "j"))
    (.seq (.ite hashDeleteEmpty .break .skip) hashDeleteLoopRest)

/-- Deletion advances j before testing occupancy; moving entries changes i,
so the cyclic termination rank must follow j rather than the hole i. -/
theorem source_htabDelete_loop :
    hashDeleteLeadingWhile (sourceFunctionBody Guest.guestFn_htab_del) =
      some (.const 1,hashDeleteLoopBody) := by
  unfold hashDeleteLoopBody hashDeleteLoopRest
  simp only [sourceFunctionBody,declToHOL_eq]
  simp only [Guest.guestFn_htab_del,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile,hashDeleteEmpty,hashProbeStep]
  rfl

/-- Starting with the pre-incremented scan position reaches any empty slot
within at most capacity loop iterations, including wraparound. -/
theorem hashDelete_scan_reaches (capacity empty index : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat)
    (emptyInside : empty.toNat < capacity.toNat) :
    ∃ steps, steps + 1 ≤ capacity.toNat ∧
      hashProbeAdvance capacity steps (hashProbeNext index capacity) = empty := by
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits power inside]
    exact Nat.mod_lt _ positive
  obtain ⟨steps,bounded,reaches⟩ := hashProbeAdvance_reaches capacity empty bits power emptyInside
    (hashProbeNext index capacity) nextInside
  have distance := hashProbeDistance_lt_capacity capacity.toNat
    (hashProbeNext index capacity).toNat empty.toNat nextInside emptyInside
  exact ⟨steps,by omega,reaches⟩

#print axioms source_htabDelete_loop
#print axioms hashDelete_scan_reaches
end InitECandidate.Runtime
