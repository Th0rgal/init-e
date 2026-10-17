import InitECandidate.Runtime.HeaderLoadScope
import InitECandidate.Runtime.HashInsertTableMemory
import InitECandidate.Runtime.HashInsertHashMemorySupported
set_option linter.unusedSimpArgs false
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original insertion body for supported aligned key widths. -/
theorem evaluate_source_hashInsert_supported_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride key capacity used values value order orderPos count keyLength : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word keyLength)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain64 : state.memaddrs (table + 64)) (cell64 : state.memory (table + 64) = .word orderPos)
    (facts : HashInsertTableMemory capacity used table values order orderPos count state)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) (fits : keyLength.toNat ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 2 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
          watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧
          watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) →
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
          watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) →
        watched ≠ order + count * 8 → watched ≠ table + 24 → post.memory watched = state.memory watched := by
  have n0_1 : ofString "cap" ≠ ofString "klen" := by decide
  have n0_2 : ofString "cap" ≠ ofString "stride" := by decide
  have n0_3 : ofString "cap" ≠ ofString "keys" := by decide
  have n0_4 : ofString "cap" ≠ ofString "used" := by decide
  have n0_5 : ofString "cap" ≠ ofString "order" := by decide
  have n0_6 : ofString "cap" ≠ ofString "order_pos" := by decide
  have n0_7 : ofString "cap" ≠ ofString "t" := by decide
  have n0_8 : ofString "cap" ≠ ofString "key" := by decide
  have n0_9 : ofString "cap" ≠ ofString "value" := by decide
  have n1_2 : ofString "klen" ≠ ofString "stride" := by decide
  have n1_3 : ofString "klen" ≠ ofString "keys" := by decide
  have n1_4 : ofString "klen" ≠ ofString "used" := by decide
  have n1_5 : ofString "klen" ≠ ofString "order" := by decide
  have n1_6 : ofString "klen" ≠ ofString "order_pos" := by decide
  have n1_7 : ofString "klen" ≠ ofString "t" := by decide
  have n1_8 : ofString "klen" ≠ ofString "key" := by decide
  have n1_9 : ofString "klen" ≠ ofString "value" := by decide
  have n2_3 : ofString "stride" ≠ ofString "keys" := by decide
  have n2_4 : ofString "stride" ≠ ofString "used" := by decide
  have n2_5 : ofString "stride" ≠ ofString "order" := by decide
  have n2_6 : ofString "stride" ≠ ofString "order_pos" := by decide
  have n2_7 : ofString "stride" ≠ ofString "t" := by decide
  have n2_8 : ofString "stride" ≠ ofString "key" := by decide
  have n2_9 : ofString "stride" ≠ ofString "value" := by decide
  have n3_4 : ofString "keys" ≠ ofString "used" := by decide
  have n3_5 : ofString "keys" ≠ ofString "order" := by decide
  have n3_6 : ofString "keys" ≠ ofString "order_pos" := by decide
  have n3_7 : ofString "keys" ≠ ofString "t" := by decide
  have n3_8 : ofString "keys" ≠ ofString "key" := by decide
  have n3_9 : ofString "keys" ≠ ofString "value" := by decide
  have n4_5 : ofString "used" ≠ ofString "order" := by decide
  have n4_6 : ofString "used" ≠ ofString "order_pos" := by decide
  have n4_7 : ofString "used" ≠ ofString "t" := by decide
  have n4_8 : ofString "used" ≠ ofString "key" := by decide
  have n4_9 : ofString "used" ≠ ofString "value" := by decide
  have n5_6 : ofString "order" ≠ ofString "order_pos" := by decide
  have n5_7 : ofString "order" ≠ ofString "t" := by decide
  have n5_8 : ofString "order" ≠ ofString "key" := by decide
  have n5_9 : ofString "order" ≠ ofString "value" := by decide
  have n6_7 : ofString "order_pos" ≠ ofString "t" := by decide
  have n6_8 : ofString "order_pos" ≠ ofString "key" := by decide
  have n6_9 : ofString "order_pos" ≠ ofString "value" := by decide
  let s1 := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have t1 : state.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run1 : ∀ continuation, evaluateHOLFiniteState state
      (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) continuation) =
      (let output := evaluateHOLFiniteState s1 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "cap",state.locals.lookup (ofString "cap")))})) := by
    intro continuation
    exact evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity continuation t1 domain16 cell16
  let s2 := setVarHOLFinite (ofString "klen") (.val (.word keyLength)) s1
  have t2 : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run2 : ∀ continuation, evaluateHOLFiniteState s1
      (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0)) continuation) =
      (let output := evaluateHOLFiniteState s2 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "klen",s1.locals.lookup (ofString "klen")))})) := by
    intro continuation
    exact evaluate_header_load_scope s1 (ofString "klen") (ofString "t") table 0 keyLength continuation t2 domain0 cell0
  let s3 := setVarHOLFinite (ofString "stride") (.val (.word stride)) s2
  have t3 : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run3 : ∀ continuation, evaluateHOLFiniteState s2
      (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8)) continuation) =
      (let output := evaluateHOLFiniteState s3 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "stride",s2.locals.lookup (ofString "stride")))})) := by
    intro continuation
    exact evaluate_header_load_scope s2 (ofString "stride") (ofString "t") table 8 stride continuation t3 domain8 cell8
  let s4 := setVarHOLFinite (ofString "keys") (.val (.word keys)) s3
  have t4 : s3.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run4 : ∀ continuation, evaluateHOLFiniteState s3
      (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32)) continuation) =
      (let output := evaluateHOLFiniteState s4 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "keys",s3.locals.lookup (ofString "keys")))})) := by
    intro continuation
    exact evaluate_header_load_scope s3 (ofString "keys") (ofString "t") table 32 keys continuation t4 domain32 cell32
  let s5 := setVarHOLFinite (ofString "used") (.val (.word used)) s4
  have t5 : s4.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run5 : ∀ continuation, evaluateHOLFiniteState s4
      (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48)) continuation) =
      (let output := evaluateHOLFiniteState s5 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "used",s4.locals.lookup (ofString "used")))})) := by
    intro continuation
    exact evaluate_header_load_scope s4 (ofString "used") (ofString "t") table 48 used continuation t5 domain48 cell48
  let s6 := setVarHOLFinite (ofString "order") (.val (.word order)) s5
  have t6 : s5.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run6 : ∀ continuation, evaluateHOLFiniteState s5
      (.dec (ofString "order") .one (.load .one (hashLocalAddress (ofString "t") 56)) continuation) =
      (let output := evaluateHOLFiniteState s6 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "order",s5.locals.lookup (ofString "order")))})) := by
    intro continuation
    exact evaluate_header_load_scope s5 (ofString "order") (ofString "t") table 56 order continuation t6 domain56 cell56
  let s7 := setVarHOLFinite (ofString "order_pos") (.val (.word orderPos)) s6
  have t7 : s6.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run7 : ∀ continuation, evaluateHOLFiniteState s6
      (.dec (ofString "order_pos") .one (.load .one (hashLocalAddress (ofString "t") 64)) continuation) =
      (let output := evaluateHOLFiniteState s7 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "order_pos",s6.locals.lookup (ofString "order_pos")))})) := by
    intro continuation
    exact evaluate_header_load_scope s6 (ofString "order_pos") (ofString "t") table 64 orderPos continuation t7 domain64 cell64
  have capBinding : s7.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have klenBinding : s7.locals.lookup (ofString "klen") = some (.val (.word keyLength)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have strideBinding : s7.locals.lookup (ofString "stride") = some (.val (.word stride)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have keysBinding : s7.locals.lookup (ofString "keys") = some (.val (.word keys)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have usedBinding : s7.locals.lookup (ofString "used") = some (.val (.word used)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have orderBinding : s7.locals.lookup (ofString "order") = some (.val (.word order)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have orderPosBinding : s7.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have tableBinding : s7.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have keyBinding : s7.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using keyLocal
  have valueBinding : s7.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using valueLocal
  have environment := HashInsertTableMemory.enter capacity used table values value order orderPos count state s7
    facts rfl rfl rfl tableBinding orderBinding orderPosBinding usedBinding valueBinding
  obtain ⟨post,tail,header,agreement,cost,remaining,globals,postCode,addresses,endian,frame⟩ := evaluate_hashInsert_hash_scope_supported_memory s7
    capacity used table values value order orderPos count keys stride key keyLength bits power code supported
    capBinding usedBinding keysBinding strideBinding keyBinding klenBinding
    (by change capacity.toNat + keyLength.toNat + 2 ≤ state.clock; omega) readable room environment
    keysAligned strideAligned keyAligned usedAligned headerBefore keysBefore usedBound fits
    arrayDomain sourceWordDomain sourceByteDomain
  rw [source_htabInsert_header_prefix,run1]
  dsimp only
  rw [run2]
  dsimp only
  rw [run3]
  dsimp only
  rw [run4]
  dsimp only
  rw [run5]
  dsimp only
  rw [run6]
  dsimp only
  rw [run7]
  dsimp only
  rw [tail]
  change state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2 at cost
  exact ⟨_,rfl,header,agreement,by change state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2; omega,remaining,globals,postCode,addresses,endian,frame⟩

#print axioms evaluate_source_hashInsert_supported_memory
end InitECandidate.Runtime
