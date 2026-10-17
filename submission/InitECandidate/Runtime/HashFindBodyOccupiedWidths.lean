import InitECandidate.Runtime.HeaderLoadScope
import InitECandidate.Runtime.HashFindHashScopeOccupiedWidths
set_option linter.unusedSimpArgs false
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_source_hashFind20_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word (20 : BitVec 64))
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyWords : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (budget : 2 * capacity.toNat + 1 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_find_slot) =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead post used found ≠ some 0) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have n01 : ofString "cap" ≠ ofString "klen" := by decide
  have n02 : ofString "cap" ≠ ofString "stride" := by decide
  have n03 : ofString "cap" ≠ ofString "keys" := by decide
  have n04 : ofString "cap" ≠ ofString "used" := by decide
  have n05 : ofString "cap" ≠ ofString "t" := by decide
  have n06 : ofString "cap" ≠ ofString "key" := by decide
  have n12 : ofString "klen" ≠ ofString "stride" := by decide
  have n13 : ofString "klen" ≠ ofString "keys" := by decide
  have n14 : ofString "klen" ≠ ofString "used" := by decide
  have n15 : ofString "klen" ≠ ofString "t" := by decide
  have n16 : ofString "klen" ≠ ofString "key" := by decide
  have n23 : ofString "stride" ≠ ofString "keys" := by decide
  have n24 : ofString "stride" ≠ ofString "used" := by decide
  have n25 : ofString "stride" ≠ ofString "t" := by decide
  have n26 : ofString "stride" ≠ ofString "key" := by decide
  have n34 : ofString "keys" ≠ ofString "used" := by decide
  have n35 : ofString "keys" ≠ ofString "t" := by decide
  have n36 : ofString "keys" ≠ ofString "key" := by decide
  have n45 : ofString "used" ≠ ofString "t" := by decide
  have n46 : ofString "used" ≠ ofString "key" := by decide
  let s1 := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have t1 : state.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load1 := evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity
  have run1 : ∀ continuation, evaluateHOLFiniteState state
      (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) continuation) =
      (let output := evaluateHOLFiniteState s1 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "cap",state.locals.lookup (ofString "cap")))})) := by
    intro continuation
    exact load1 continuation t1 domain16 cell16
  let s2 := setVarHOLFinite (ofString "klen") (.val (.word (20 : BitVec 64))) s1
  have t2 : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load2 := evaluate_header_load_scope s1 (ofString "klen") (ofString "t") table 0 (20 : BitVec 64)
  have run2 : ∀ continuation, evaluateHOLFiniteState s1
      (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0)) continuation) =
      (let output := evaluateHOLFiniteState s2 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "klen",s1.locals.lookup (ofString "klen")))})) := by
    intro continuation
    exact load2 continuation t2 domain0 cell0
  let s3 := setVarHOLFinite (ofString "stride") (.val (.word stride)) s2
  have t3 : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load3 := evaluate_header_load_scope s2 (ofString "stride") (ofString "t") table 8 stride
  have run3 : ∀ continuation, evaluateHOLFiniteState s2
      (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8)) continuation) =
      (let output := evaluateHOLFiniteState s3 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "stride",s2.locals.lookup (ofString "stride")))})) := by
    intro continuation
    exact load3 continuation t3 domain8 cell8
  let s4 := setVarHOLFinite (ofString "keys") (.val (.word keys)) s3
  have t4 : s3.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load4 := evaluate_header_load_scope s3 (ofString "keys") (ofString "t") table 32 keys
  have run4 : ∀ continuation, evaluateHOLFiniteState s3
      (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32)) continuation) =
      (let output := evaluateHOLFiniteState s4 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "keys",s3.locals.lookup (ofString "keys")))})) := by
    intro continuation
    exact load4 continuation t4 domain32 cell32
  let s5 := setVarHOLFinite (ofString "used") (.val (.word used)) s4
  have t5 : s4.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load5 := evaluate_header_load_scope s4 (ofString "used") (ofString "t") table 48 used
  have run5 : ∀ continuation, evaluateHOLFiniteState s4
      (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48)) continuation) =
      (let output := evaluateHOLFiniteState s5 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "used",s4.locals.lookup (ofString "used")))})) := by
    intro continuation
    exact load5 continuation t5 domain48 cell48
  have environment : HashFindEnvironment 20 keys stride key capacity used s5 := by
    refine ⟨code,?_,?_,?_,?_,?_,?_,arrayDomain,keyWords,keyBytes,readable,room⟩
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simpa [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using keyLocal
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
  obtain ⟨found,post,tail,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian⟩ := evaluate_hashFindHashScope20_occupied table keys stride capacity used values order orderPos count key bits power
    keyAligned s5 environment
      (HashTableArraysInvariant.after_read state s5 _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) budget
  rw [source_htabFind_header_prefix,run1]
  dsimp only
  rw [run2]
  dsimp only
  rw [run3]
  dsimp only
  rw [run4]
  dsimp only
  rw [run5]
  dsimp only
  rw [tail]
  exact ⟨found,_,rfl,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian⟩


theorem evaluate_source_hashFind52_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word (52 : BitVec 64))
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyWords : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (budget : 2 * capacity.toNat + 1 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_find_slot) =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead post used found ≠ some 0) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have n01 : ofString "cap" ≠ ofString "klen" := by decide
  have n02 : ofString "cap" ≠ ofString "stride" := by decide
  have n03 : ofString "cap" ≠ ofString "keys" := by decide
  have n04 : ofString "cap" ≠ ofString "used" := by decide
  have n05 : ofString "cap" ≠ ofString "t" := by decide
  have n06 : ofString "cap" ≠ ofString "key" := by decide
  have n12 : ofString "klen" ≠ ofString "stride" := by decide
  have n13 : ofString "klen" ≠ ofString "keys" := by decide
  have n14 : ofString "klen" ≠ ofString "used" := by decide
  have n15 : ofString "klen" ≠ ofString "t" := by decide
  have n16 : ofString "klen" ≠ ofString "key" := by decide
  have n23 : ofString "stride" ≠ ofString "keys" := by decide
  have n24 : ofString "stride" ≠ ofString "used" := by decide
  have n25 : ofString "stride" ≠ ofString "t" := by decide
  have n26 : ofString "stride" ≠ ofString "key" := by decide
  have n34 : ofString "keys" ≠ ofString "used" := by decide
  have n35 : ofString "keys" ≠ ofString "t" := by decide
  have n36 : ofString "keys" ≠ ofString "key" := by decide
  have n45 : ofString "used" ≠ ofString "t" := by decide
  have n46 : ofString "used" ≠ ofString "key" := by decide
  let s1 := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have t1 : state.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load1 := evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity
  have run1 : ∀ continuation, evaluateHOLFiniteState state
      (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) continuation) =
      (let output := evaluateHOLFiniteState s1 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "cap",state.locals.lookup (ofString "cap")))})) := by
    intro continuation
    exact load1 continuation t1 domain16 cell16
  let s2 := setVarHOLFinite (ofString "klen") (.val (.word (52 : BitVec 64))) s1
  have t2 : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load2 := evaluate_header_load_scope s1 (ofString "klen") (ofString "t") table 0 (52 : BitVec 64)
  have run2 : ∀ continuation, evaluateHOLFiniteState s1
      (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0)) continuation) =
      (let output := evaluateHOLFiniteState s2 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "klen",s1.locals.lookup (ofString "klen")))})) := by
    intro continuation
    exact load2 continuation t2 domain0 cell0
  let s3 := setVarHOLFinite (ofString "stride") (.val (.word stride)) s2
  have t3 : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load3 := evaluate_header_load_scope s2 (ofString "stride") (ofString "t") table 8 stride
  have run3 : ∀ continuation, evaluateHOLFiniteState s2
      (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8)) continuation) =
      (let output := evaluateHOLFiniteState s3 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "stride",s2.locals.lookup (ofString "stride")))})) := by
    intro continuation
    exact load3 continuation t3 domain8 cell8
  let s4 := setVarHOLFinite (ofString "keys") (.val (.word keys)) s3
  have t4 : s3.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load4 := evaluate_header_load_scope s3 (ofString "keys") (ofString "t") table 32 keys
  have run4 : ∀ continuation, evaluateHOLFiniteState s3
      (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32)) continuation) =
      (let output := evaluateHOLFiniteState s4 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "keys",s3.locals.lookup (ofString "keys")))})) := by
    intro continuation
    exact load4 continuation t4 domain32 cell32
  let s5 := setVarHOLFinite (ofString "used") (.val (.word used)) s4
  have t5 : s4.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using tableLocal
  have load5 := evaluate_header_load_scope s4 (ofString "used") (ofString "t") table 48 used
  have run5 : ∀ continuation, evaluateHOLFiniteState s4
      (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48)) continuation) =
      (let output := evaluateHOLFiniteState s5 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "used",s4.locals.lookup (ofString "used")))})) := by
    intro continuation
    exact load5 continuation t5 domain48 cell48
  have environment : HashFindEnvironment 52 keys stride key capacity used s5 := by
    refine ⟨code,?_,?_,?_,?_,?_,?_,arrayDomain,keyWords,keyBytes,readable,room⟩
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simpa [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46] using keyLocal
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
    · simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,n34,n35,n36,n45,n46]
  obtain ⟨found,post,tail,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian⟩ := evaluate_hashFindHashScope52_occupied table keys stride capacity used values order orderPos count key bits power
    keyAligned s5 environment
      (HashTableArraysInvariant.after_read state s5 _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) budget
  rw [source_htabFind_header_prefix,run1]
  dsimp only
  rw [run2]
  dsimp only
  rw [run3]
  dsimp only
  rw [run4]
  dsimp only
  rw [run5]
  dsimp only
  rw [tail]
  exact ⟨found,_,rfl,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian⟩


#print axioms evaluate_source_hashFind20_occupied
#print axioms evaluate_source_hashFind52_occupied
end InitECandidate.Runtime
