import InitECandidate.Runtime.RlpBeLenCountBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A successful exact code lookup yields a successful finite code lookup with the same body and
return shape; only the callee-local map is re-rendered with its finite-support witness. -/
theorem lookupCodeHOLFinite_of_exact (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname : MlS) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (calleeLocals : MlS → Option (ValueHOL 64)) (returnShape : ShapeHOL)
    (exact : lookupCodeHOLExact code fname values = some (body,calleeLocals,returnShape)) :
    ∃ callee, PanSemStateFiniteExact.lookupCodeHOLFinite code fname values =
      some (body,callee,returnShape) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i hnone
    rw [exact] at hnone
    cases hnone
  · rename_i hsome
    rw [exact] at hsome
    cases hsome
    exact ⟨_,rfl⟩

#print axioms lookupCodeHOLFinite_of_exact

/-- The exact code lookup of `rlp_be_len` binds its single parameter `v`. -/
theorem rlpBeLen_exact_lookup (N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_be_len") [.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_be_len,
        (fun x => if x = ofString "v" then (some (.val (.word N)) : Option (ValueHOL 64)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_be_len_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpBeLen_exact_lookup

/-- The exact code lookup of `rlp_put_be` binds its three parameters. -/
theorem rlpPutBe_exact_lookup (D V N : BitVec 64) :
    lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_put_be")
      [.val (.word D),.val (.word V),.val (.word N)] =
      some (sourceFunctionBody Guest.guestFn_rlp_put_be,
        (fun x => if x = ofString "n" then (some (.val (.word N)) : Option (ValueHOL 64))
                  else if x = ofString "v" then some (.val (.word V))
                  else if x = ofString "dst" then some (.val (.word D)) else none), .one) := by
  rw [lookupCodeHOLExact,originalRuntimeCode_rlp_put_be_lookup]
  dsimp only
  rw [if_pos]
  · simp
  · refine ⟨by decide,rfl,?_⟩
    simp [shapeOfHOLExact,shapeEqHOL]

#print axioms rlpPutBe_exact_lookup

/-- **The actual `rlp_be_len` call binds `v`.** A successful finite lookup of the installed
`rlp_be_len` on one word argument has the installed body, a one-word return shape, and reads that
word back as `v`. -/
theorem rlpBeLen_call_facts (N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_be_len") [.val (.word N)] = some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_be_len ∧
      returnShape = .one ∧ callee.lookup (ofString "v") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpBeLen_exact_lookup N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    rw [← hcallee]
    simp

#print axioms rlpBeLen_call_facts

/-- **The actual `rlp_put_be` call binds `dst`, `v` and `n`.** A successful finite lookup of the
installed three-parameter writer on three word arguments has the installed body, a one-word return
shape, and reads those words back under their parameter names. -/
theorem rlpPutBe_call_facts (D V N : BitVec 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rlp_put_be") [.val (.word D),.val (.word V),.val (.word N)] =
        some (body,callee,returnShape)) :
    body = sourceFunctionBody Guest.guestFn_rlp_put_be ∧
      returnShape = .one ∧
      callee.lookup (ofString "dst") = some (.val (.word D)) ∧
      callee.lookup (ofString "v") = some (.val (.word V)) ∧
      callee.lookup (ofString "n") = some (.val (.word N)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i ebody ecl ers raw
    simp only [rlpPutBe_exact_lookup D V N] at raw
    simp only [Option.some.injEq,Prod.mk.injEq] at raw
    obtain ⟨rfl,rfl,rfl⟩ := raw
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨hbody,hcallee,hshape⟩ := found
    refine ⟨hbody.symm,hshape.symm,?_⟩
    refine ⟨?_,?_,?_⟩ <;> (rw [← hcallee] <;> simp +decide)

#print axioms rlpPutBe_call_facts

end InitECandidate.Runtime
