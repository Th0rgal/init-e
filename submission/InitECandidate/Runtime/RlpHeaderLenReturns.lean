import InitECandidate.Runtime.RlpEncodeListHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- An `if` whose only returning branch is `return 1` only ever returns `1`. -/
theorem iteReturnOne_returns_one {F : Type} (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (r : ValueHOL 64)
    (run : (evaluateHOLFiniteState s (.ite cond (.return (.const (1#64))) .skip)).1 =
      some (.returned r)) : r = .val (.word (1#64)) := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      simp at run
    · rw [if_neg hz,evaluateHOLFiniteState_return] at run
      simp only [evalHOLExact] at run
      split at run
      · injection run with h
        injection h with h
        exact h.symm
      · simp at run
  · simp at run

#print axioms iteReturnOne_returns_one

/-- An `if` whose only returning branch is `return 1` continues only unchanged. -/
theorem iteReturnOne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s (.ite cond (.return (.const (1#64))) .skip) = (none, mid)) :
    mid = s := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      obtain ⟨_,h⟩ := Prod.mk.inj run
      exact h.symm
    · rw [if_neg hz,evaluateHOLFiniteState_return] at run
      simp only [evalHOLExact] at run
      split at run <;> simp at run
  · obtain ⟨_,h⟩ := Prod.mk.inj run
    exact h.symm

#print axioms iteReturnOne_none

/-- The exact code lookup of `rlp_header_len` binds its single parameter `n`. -/
theorem rlpHeaderLen_exact_lookup (N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_header_len")
      [.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_header_len,
        (fun x => if x = ofString "n" then (some (.val (.word N)) : Option (ValueHOL 64)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_header_len_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpHeaderLen_exact_lookup

/-- A successful finite lookup of the installed `rlp_header_len` on one word argument has the
installed body, a one-word return shape, and reads that word back as `n`. -/
theorem rlpHeaderLen_call_facts (N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_header_len") [.val (.word N)] = some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_header_len ∧ returnShape = .one ∧
      callee.lookup (ofString "n") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpHeaderLen_exact_lookup N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    rw [← hcallee]
    simp

#print axioms rlpHeaderLen_call_facts

/-- The exact code lookup of `rlp_list_header_len` binds its parameter `payload_len`. -/
theorem rlpListHeaderLen_exact_lookup (P : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_list_header_len")
      [.val (.word P)] =
      some (sourceFunctionBody Guest.guestFn_rlp_list_header_len,
        (fun x => if x = ofString "payload_len" then (some (.val (.word P)) : Option (ValueHOL 64)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_list_header_len_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpListHeaderLen_exact_lookup

/-- A successful finite lookup of the installed `rlp_list_header_len` on one word argument has the
installed body, a one-word return shape, and reads that word back as `payload_len`. -/
theorem rlpListHeaderLen_call_facts (P : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_list_header_len") [.val (.word P)] = some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_list_header_len ∧ returnShape = .one ∧
      callee.lookup (ofString "payload_len") = some (.val (.word P)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpListHeaderLen_exact_lookup P] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    rw [← hcallee]
    simp

#print axioms rlpListHeaderLen_call_facts

end InitECandidate.Runtime
