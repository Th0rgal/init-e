import InitECandidate.Runtime.HashFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute all four actual32-byte hash loads and final mix. The complete
fast path returns at zero source-clock cost and preserves nonlocal state. -/
theorem evaluate_hashFast32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord v0 v8 v16 v24 : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (domain0 : state.memaddrs (pointer + BitVec.ofNat 64 0))
    (cell0 : state.memory (pointer + BitVec.ofNat 64 0) = .word v0)
    (domain8 : state.memaddrs (pointer + BitVec.ofNat 64 8))
    (cell8 : state.memory (pointer + BitVec.ofNat 64 8) = .word v8)
    (domain16 : state.memaddrs (pointer + BitVec.ofNat 64 16))
    (cell16 : state.memory (pointer + BitVec.ofNat 64 16) = .word v16)
    (domain24 : state.memaddrs (pointer + BitVec.ofNat 64 24))
    (cell24 : state.memory (pointer + BitVec.ofNat 64 24) = .word v24)
    : ∃ post, evaluateHOLFiniteState state hashFast32 =
      (some (.returned (.val (.word (hashFinishValue ((((hash ^^^ v0) ^^^ v8) ^^^ v16) ^^^ v24))))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have hp : ofString "h" ≠ ofString "p" := by decide
  have wp : ofString "w" ≠ ofString "p" := by decide
  have hw : ofString "h" ≠ ofString "w" := by decide
  let s1 := setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ v0)))
    (setVarHOLFinite (ofString "w") (.val (.word v0)) state)
  have run1 := evaluate_hashWordThen state pointer hash oldWord v0 0 (hashWordThen 8 (hashWordThen 16 (hashWordThen 24 hashFinish)))
    pointerLocal hashLocal wordLocal domain0 cell0
  let s2 := setVarHOLFinite (ofString "h") (.val (.word ((hash ^^^ v0) ^^^ v8)))
    (setVarHOLFinite (ofString "w") (.val (.word v8)) s1)
  have p2 : s1.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have h2 : s1.locals.lookup (ofString "h") = some (.val (.word (hash ^^^ v0))) := by
    simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have w2 : s1.locals.lookup (ofString "w") = some (.val (.word v0)) := by
    simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have run2 := evaluate_hashWordThen s1 pointer (hash ^^^ v0) v0 v8 8 (hashWordThen 16 (hashWordThen 24 hashFinish))
    p2 h2 w2 domain8 cell8
  let s3 := setVarHOLFinite (ofString "h") (.val (.word (((hash ^^^ v0) ^^^ v8) ^^^ v16)))
    (setVarHOLFinite (ofString "w") (.val (.word v16)) s2)
  have p3 : s2.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have h3 : s2.locals.lookup (ofString "h") = some (.val (.word ((hash ^^^ v0) ^^^ v8))) := by
    simp [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have w3 : s2.locals.lookup (ofString "w") = some (.val (.word v8)) := by
    simp [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have run3 := evaluate_hashWordThen s2 pointer ((hash ^^^ v0) ^^^ v8) v8 v16 16 (hashWordThen 24 hashFinish)
    p3 h3 w3 domain16 cell16
  let s4 := setVarHOLFinite (ofString "h") (.val (.word ((((hash ^^^ v0) ^^^ v8) ^^^ v16) ^^^ v24)))
    (setVarHOLFinite (ofString "w") (.val (.word v24)) s3)
  have p4 : s3.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have h4 : s3.locals.lookup (ofString "h") = some (.val (.word (((hash ^^^ v0) ^^^ v8) ^^^ v16))) := by
    simp [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have w4 : s3.locals.lookup (ofString "w") = some (.val (.word v16)) := by
    simp [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,hw,pointerLocal]
  have run4 := evaluate_hashWordThen s3 pointer (((hash ^^^ v0) ^^^ v8) ^^^ v16) v16 v24 24 hashFinish
    p4 h4 w4 domain24 cell24
  have hFinal : s4.locals.lookup (ofString "h") = some (.val (.word ((((hash ^^^ v0) ^^^ v8) ^^^ v16) ^^^ v24))) := by
    simp [s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have finish := evaluate_hashFinish s4 ((((hash ^^^ v0) ^^^ v8) ^^^ v16) ^^^ v24) hFinal
  rw [source_hash_fast32,run1,run2,run3,run4,finish]
  exact ⟨_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_hashFast32
end InitECandidate.Runtime
