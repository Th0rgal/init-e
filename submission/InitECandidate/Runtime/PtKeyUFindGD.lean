import InitECandidate.Runtime.PtKeyUMemeqBodyGD
import InitECandidate.Runtime.PtKeyUFindLoopGD
import InitECandidate.Runtime.MemeqCall20
import InitECandidate.Runtime.HashFindTableLoop20
/-!
The source lookup loop for 20/32/52-byte keys at any key alignment.  Each occupied probe calls the actual `memeq`
(`evaluate_source_memeqK`), so it spends between two and `n + 2` clocks; the loop is bounded by `(n + 2)` times the
cyclic probe distance.  The key only needs addressable aligned cells for its bytes (`HashFindInvariant.keyBytes`) and
to fit below the top of the address space; no key alignment is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section fk
variable {F : Type}

/-- The actual `memeq` declaration-call for a supported width at any operand alignment. -/
theorem evaluate_memeqK_declaration (state : PanSemStateFiniteExact 64 F)
    (aArgument bArgument sizeArgument : ExpHOL 64) (a b n : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [aArgument,bArgument,sizeArgument] =
        some [.val (.word a),.val (.word b),.val (.word n)])
    (code : state.code = originalRuntimeCode) (sup : n = 20 ∨ n = 32 ∨ n = 52) (clock : n.toNat + 1 ≤ state.clock)
    (fitA : a.toNat + n.toNat < 2 ^ 64) (fitB : b.toNat + n.toNat < 2 ^ 64)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      state.memaddrs (panByteAlignHOL (a + x)) ∧ state.memaddrs (panByteAlignHOL (b + x))) :
    ∃ value : BitVec 64, ∃ ready, (value = 0 ∨ value = 1) ∧
      ready.clock ≤ state.clock - 1 ∧ state.clock - 1 ≤ ready.clock + n.toNat ∧ ready.memory = state.memory ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "memeq") [aArgument,bArgument,sizeArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "a",.val (.word a))).update
      (ofString "b",.val (.word b))).update (ofString "n",.val (.word n))
  let entry := callEntryStateHOLFinite state callee
  have na : ofString "n" ≠ ofString "a" := by decide
  have nb : ofString "n" ≠ ofString "b" := by decide
  have ba : ofString "b" ≠ ofString "a" := by decide
  have aLocal : entry.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,na,ba]
  have bLocal : entry.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,nb]
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,boolean,body,lo,hi,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_memeqK entry a b n aLocal bLocal sizeLocal sup fitA fitB cells
      (by change n.toNat ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "memeq") =
      some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
    rw [code]; exact originalRuntimeCode_memeq_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memeq) a b n (by decide) (by decide) (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word value))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨value,{post with locals := state.locals},boolean,lo,hi,memory,rfl,globals,postCode,addresses,endian,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "memeq") .one .one
    [aArgument,bArgument,sizeArgument] [.val (.word a),.val (.word b),.val (.word n)]
    (sourceFunctionBody Guest.guestFn_memeq) continuation callee (.val (.word value))
    arguments lookup (by omega) body lo shapeOk shapeOk

/-- An occupied-probe iteration at any key alignment: return the index or advance the probe, in `1..n+1` clocks. -/
theorem evaluate_hashFind_iterationK (state : PanSemStateFiniteExact 64 F)
    (a b n index capacity : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word a),.val (.word b),.val (.word n)])
    (code : state.code = originalRuntimeCode) (sup : n = 20 ∨ n = 32 ∨ n = 52) (clock : n.toNat + 1 ≤ state.clock)
    (fitA : a.toNat + n.toNat < 2 ^ 64) (fitB : b.toNat + n.toNat < 2 ^ 64)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      state.memaddrs (panByteAlignHOL (a + x)) ∧ state.memaddrs (panByteAlignHOL (b + x)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    ∃ result post, evaluateHOLFiniteState state hashFindIteration = (result,post) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock ≤ state.clock - 1 ∧ state.clock - 1 ≤ post.clock + n.toNat ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity)))) ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  obtain ⟨value,ready,boolean,lo,hi,memory,locals,globals,postCode,addresses,endian,decl⟩ :=
    evaluate_memeqK_declaration state _ _ _ a b n arguments code sup clock fitA fitB cells
  let entered := setVarHOLFinite (ofString "eq") (.val (.word value)) ready
  have ni : ofString "eq" ≠ ofString "i" := by decide
  have nc : ofString "eq" ≠ ofString "cap" := by decide
  have i : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ni,locals] using indexLocal
  have c : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have e : entered.locals.lookup (ofString "eq") = some (.val (.word value)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  unfold hashFindIteration
  rw [decl]
  rcases boolean with zero | one
  · have run := evaluate_hashFind_mismatch entered index capacity i c (by rw [zero] at e; exact e)
    change ∃ result post, (let output := evaluateHOLFiniteState entered hashFindDecision; _) = _ ∧ _
    rw [run]
    refine ⟨none,_,rfl,Or.inl rfl,lo,hi,memory,globals,postCode,addresses,endian,?_⟩
    constructor
    · intro _
      rw [restore_other_local _ (ofString "eq") (ofString "i") _ (by decide)]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro _
      change HolFiniteMapExact.resVarEq
        ((ready.locals.update (ofString "eq",.val (.word value))).update
          (ofString "i",.val (.word (hashProbeNext index capacity))))
        (ofString "eq",state.locals.lookup (ofString "eq")) = _
      rw [locals]
      exact restore_updated_other_local state.locals (ofString "eq") (ofString "i") _ _ ni
  · have nonzero : value ≠ 0 := by rw [one]; decide
    have run := evaluate_hashFind_match entered index value nonzero i e
    change ∃ result post, (let output := evaluateHOLFiniteState entered hashFindDecision; _) = _ ∧ _
    rw [run]
    refine ⟨_,_,rfl,Or.inr rfl,lo,hi,memory,globals,postCode,addresses,endian,?_⟩
    constructor <;> intro impossible <;> cases impossible

/-- Byte cells of a range from its offset form. -/
theorem cells_of_offsets {D : BitVec 64 → Prop} (a n : BitVec 64)
    (h : ∀ offset : Nat, offset < n.toNat → D (panByteAlignHOL (a + BitVec.ofNat 64 offset))) :
    ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (a + x)) := by
  intro x hx
  have := h x.toNat hx
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

/-- The slot base of an in-range probe and its key bytes fit in the address space. -/
theorem hashFind_slot_fit (table keys stride capacity used values order orderPos count index n : BitVec 64) (bits : Nat)
    {state : PanSemStateFiniteExact 64 F}
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (inside : index.toNat < capacity.toNat) : (keys + index * stride).toNat + n.toNat < 2 ^ 64 := by
  have ku := arrays.keysBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have eb := arrays.endBound
  have fits := arrays.fits
  have slot := (hashFind_slot_address keys index stride capacity inside (by omega) arrays.keysAligned arrays.strideAligned).1
  have next := Nat.mul_le_mul_right stride.toNat (show index.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul, Nat.one_mul] at next
  rw [slot]; omega

/-- One occupied probe of the actual lookup loop, any key alignment: `2..n+2` clocks. -/
theorem evaluate_hashFind_table_occupiedK (state : PanSemStateFiniteExact 64 F)
    (n table keys stride capacity used values order orderPos count key empty index : BitVec 64) (bits : Nat)
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat < 2 ^ 64)
    (valid : HashFindInvariant n keys stride key capacity used empty state index)
    (invariant : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (clock : n.toNat + 2 ≤ state.clock) (inside : index.toNat < capacity.toNat)
    (byte : UInt8)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte)
    (occupied : BitVec.ofNat 64 byte.toNat ≠ 0) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop =
        (match result with | none => evaluateHOLFiniteState post hashFindLoop | some _ => (result,post)) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock ≤ state.clock ∧ state.clock ≤ post.clock + (n.toNat + 2) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  have condition := eval_hashProbeOccupied state (ofString "i") index used byte valid.indexLocal valid.usedLocal loaded
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 byte.toNat) 0 = true := by
    have nonzero : BitVec.ofNat 64 byte.toNat ≠ (0#64) := occupied
    simp [Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  let entry := decClockHOLFinite state
  have sl := invariant.key_slot_domains state n table keys stride capacity used values order orderPos count index bits inside
  have cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      entry.memaddrs (panByteAlignHOL (keys + index * stride + x)) ∧ entry.memaddrs (panByteAlignHOL (key + x)) := by
    intro x hx
    exact ⟨cells_of_offsets (D := state.memaddrs) _ n (fun off h => (sl.2 off h).2) x hx,
      cells_of_offsets (D := state.memaddrs) _ n valid.keyBytes x hx⟩
  have arguments := eval_hashFind_arguments entry keys index stride key n valid.keysLocal valid.indexLocal
    valid.strideLocal valid.keyLocal valid.lengthLocal
  obtain ⟨result,post,body,outcome,lo,hi,memory,globals,postCode,addresses,endian,_,locals⟩ :=
    evaluate_hashFind_iterationK entry (keys + index * stride) key n index capacity arguments valid.code sup
      (by change n.toNat + 1 ≤ state.clock - 1; omega)
      (hashFind_slot_fit table keys stride capacity used values order orderPos count index n bits invariant inside) keyFit
      cells valid.indexLocal valid.capLocal
  change post.clock ≤ state.clock - 1 - 1 at lo
  change state.clock - 1 - 1 ≤ post.clock + n.toNat at hi
  refine ⟨result,post,?_,outcome,by omega,by omega,memory,globals,postCode,addresses,endian,locals⟩
  unfold hashFindLoop
  rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rw [if_pos flag]
  have body' : evaluateHOLFiniteState (decClockHOLFinite state) hashFindIteration = (result,post) := body
  have fixed : fixClockHOLFinite (decClockHOLFinite state) (result,post) = (result,post) := by
    simp [fixClockHOLFinite,decClockHOLFinite,show ¬ state.clock - 1 < post.clock by omega]
  simp only [show state.clock ≠ 0 by omega,if_false,body',fixed]
  rcases outcome with noneResult | returnedResult
  · rw [noneResult]
    rfl
  · rw [returnedResult]
    rfl

/-- The actual lookup scan at any key alignment terminates within `(n + 2)` times the cyclic probe distance. -/
theorem evaluate_hashFind_table_loopK
    (n table keys stride capacity used values order orderPos count key empty : BitVec 64) (bits : Nat)
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat < 2 ^ 64)
    (emptyInside : empty.toNat < capacity.toNat)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant n keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (budget : (n.toNat + 2) * hashProbeDistance capacity.toNat index.toNat empty.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + (n.toNat + 2) * hashProbeDistance capacity.toNat index.toNat empty.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant n keys stride key capacity used empty post finalIndex ∧
        HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits post) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let combined := fun (current : PanSemStateFiniteExact 64 F) (probe : BitVec 64) => HashFindInvariant n keys stride key capacity used empty current probe ∧
    HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits current
  apply evaluate_hashFindLoop_rankC capacity empty used bits (n.toNat + 2) (by omega) arrays.power emptyInside combined
    (fun _ _ h => ⟨h.1.indexLocal,h.1.usedLocal⟩)
    (fun _ _ h => h.1.readable _ h.1.inside) (fun _ _ h => h.1.emptyLoad) ?_
    _ state index ⟨valid,arrays⟩ valid.inside rfl budget
  intro current probe byte h inside enough loaded occupied
  obtain ⟨result,post,run,outcome,lo,hi,memory,globals,code,domain,endian,locals⟩ :=
    evaluate_hashFind_table_occupiedK current n table keys stride capacity used values order orderPos count key empty probe bits
      sup keyFit h.1 h.2 enough inside byte loaded occupied
  refine ⟨result,post,?_,outcome,lo,hi,?_,memory,globals,code,domain,endian⟩
  · cases result <;> exact run
  · intro continuing
    have nextInside : (hashProbeNext probe capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat probe capacity bits arrays.power inside]
      apply Nat.mod_lt
      rw [arrays.power]
      exact Nat.two_pow_pos bits
    exact ⟨h.1.preserve n keys stride key capacity used empty current post probe _ nextInside memory code domain endian (locals continuing),
      h.2.after_read current post n table keys stride capacity used values order orderPos count bits memory code domain endian⟩

end fk
#print axioms evaluate_memeqK_declaration
#print axioms evaluate_hashFind_iterationK
#print axioms evaluate_hashFind_table_occupiedK
#print axioms evaluate_hashFind_table_loopK
end InitECandidate.Runtime
