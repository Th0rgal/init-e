import InitECandidate.Runtime.PtKeyUFindTailGD
import InitECandidate.Runtime.PtKeyUHashCallGD
import InitECandidate.Runtime.HashFindHashScopeWidths
/-!
The actual `htab_hash` declaration-call at any key alignment, and the lookup's hash and index scopes from the
environment of `htab_find_slot`, bounded by `(n + 2)` times the capacity (plus one for the hash call).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section fs
variable {F : Type}

theorem evaluate_hashK_declaration (state : PanSemStateFiniteExact 64 F)
    (pointerArgument lengthArgument : ExpHOL 64) (pointer n : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [pointerArgument,lengthArgument] =
        some [.val (.word pointer),.val (.word n)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (fits : pointer.toNat + n.toNat ≤ 33806089496)
    (bytes : ∀ j : Nat, j < n.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j))) :
    ∃ value : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.locals = state.locals ∧ ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_hash") [pointerArgument,lengthArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "key_len",.val (.word n))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "key_len" ≠ ofString "p" := by decide
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have nl : entry.locals.lookup (ofString "key_len") = some (.val (.word n)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,body,ticks,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_hashK entry pointer n p nl sup fits bytes
  have installed : state.code.lookup (ofString "htab_hash") =
      some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
    rw [code]; exact originalRuntimeCode_hash_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
    (sourceFunctionBody Guest.guestFn_htab_hash) pointer n (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word value))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨value,{post with locals := state.locals},ticks,memory,globals,postCode,addresses,endian,rfl,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "htab_hash") .one .one
    [pointerArgument,lengthArgument] [.val (.word pointer),.val (.word n)]
    (sourceFunctionBody Guest.guestFn_htab_hash) continuation callee (.val (.word value))
    arguments lookup clock body (Nat.le_of_eq ticks) shapeOk shapeOk

theorem evaluate_hashFindIndexScopeK_from_count (n table keys stride capacity used values order orderPos count key hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat < 2 ^ 64)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment n keys stride key capacity used state)
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (budget : (n.toNat + 2) * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨empty,emptyInside,emptyLoad⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used) ready.room
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have valid : HashFindInvariant n keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyWords,ready.keyBytes,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScopeK n table keys stride capacity used values order orderPos count key empty hash
    bits sup keyFit emptyInside state hashLocal ready.capLocal valid arrays budget

theorem evaluate_hashFindHashScopeK (n table keys stride capacity used values order orderPos count key : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (sup : n = 20 ∨ n = 32 ∨ n = 52)
    (keyFit : key.toNat + n.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment n keys stride key capacity used state)
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (budget : (n.toNat + 2) * capacity.toNat + 1 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindHashScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word n)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ready.keyLocal,ready.lengthLocal]
  have capPos : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  obtain ⟨hash,hashed,clock,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hashK_declaration state _ _ key n arguments ready.code (by omega) sup keyFit ready.keyBytes
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have environment : HashFindEnvironment n keys stride key capacity used entered :=
    HashFindEnvironment.after_hash n keys stride key capacity used hash state entered ready memory code addresses endian
      (by simp only [entered,setVarHOLFinite,locals])
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨found,post,tail,inside,cost,remaining,tailMemory,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
    evaluate_hashFindIndexScopeK_from_count n table keys stride capacity used values order orderPos count key hash
      bits power sup (by omega) entered environment
      (HashTableArraysInvariant.after_read state entered _ _ _ _ _ _ _ _ _ _ bits arrays memory code addresses endian) h (by omega)
  unfold hashFindHashScope
  rw [decl]
  change ∃ found post, (let output := evaluateHOLFiniteState entered hashFindIndexScope; _) = _ ∧ _
  rw [tail]
  exact ⟨found,_,rfl,inside,by change state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat + 1; omega,
    by change post.clock ≤ state.clock; omega,tailMemory.trans memory,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩

end fs
#print axioms evaluate_hashK_declaration
#print axioms evaluate_hashFindHashScopeK
end InitECandidate.Runtime
