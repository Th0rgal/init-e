import InitECandidate.Runtime.HashGrowKeysAllocation32
import InitECandidate.Runtime.HeaderLoadScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGrowHeaderLoads (continuation : ProgHOL 64) : ProgHOL 64 :=
  (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8)) (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32)) (.dec (ofString "vals") .one (.load .one (hashLocalAddress (ofString "t") 40)) (.dec (ofString "order") .one (.load .one (hashLocalAddress (ofString "t") 56)) (.dec (ofString "nitems") .one (.load .one (hashLocalAddress (ofString "t") 24)) (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"),.const 2]) continuation)))))))

theorem source_htabGrow_header_prefix : sourceFunctionBody Guest.guestFn_htab_grow =
    hashGrowHeaderLoads (hashGrowKeysAllocation (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original six header loads and doubling scope have zero clock cost;
all later scopes see their bindings and restore the saved caller environment. -/
theorem evaluate_htabGrow_header_loads {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity stride keys values order count : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain40 : state.memaddrs (table + 40)) (cell40 : state.memory (table + 40) = .word values)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    : ∃ entered, (∀ continuation, evaluateHOLFiniteState state (hashGrowHeaderLoads continuation) =
      (let output := evaluateHOLFiniteState entered continuation;
       (output.1,{output.2 with locals := (restoreGrowthLocals state.locals [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap"] output.2.locals)}))) ∧
      entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
      entered.locals.lookup (ofString "stride") = some (.val (.word stride)) ∧
      entered.locals.lookup (ofString "keys") = some (.val (.word keys)) ∧
      entered.locals.lookup (ofString "vals") = some (.val (.word values)) ∧
      entered.locals.lookup (ofString "order") = some (.val (.word order)) ∧
      entered.locals.lookup (ofString "nitems") = some (.val (.word count)) ∧
      entered.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2))) ∧
      entered.memory = state.memory ∧ entered.globals = state.globals ∧ entered.code = state.code ∧
      entered.memaddrs = state.memaddrs ∧ entered.be = state.be ∧ entered.clock = state.clock ∧
      (∀ name, name ∉ [ofString "cap",ofString "stride",ofString "keys",ofString "vals",ofString "order",ofString "nitems",ofString "ncap"] → entered.locals.lookup name = state.locals.lookup name) := by
  have n0_1 : ofString "cap" ≠ ofString "stride" := by decide
  have n0_2 : ofString "cap" ≠ ofString "keys" := by decide
  have n0_3 : ofString "cap" ≠ ofString "vals" := by decide
  have n0_4 : ofString "cap" ≠ ofString "order" := by decide
  have n0_5 : ofString "cap" ≠ ofString "nitems" := by decide
  have n0_6 : ofString "cap" ≠ ofString "ncap" := by decide
  have n0_7 : ofString "cap" ≠ ofString "t" := by decide
  have n1_2 : ofString "stride" ≠ ofString "keys" := by decide
  have n1_3 : ofString "stride" ≠ ofString "vals" := by decide
  have n1_4 : ofString "stride" ≠ ofString "order" := by decide
  have n1_5 : ofString "stride" ≠ ofString "nitems" := by decide
  have n1_6 : ofString "stride" ≠ ofString "ncap" := by decide
  have n1_7 : ofString "stride" ≠ ofString "t" := by decide
  have n2_3 : ofString "keys" ≠ ofString "vals" := by decide
  have n2_4 : ofString "keys" ≠ ofString "order" := by decide
  have n2_5 : ofString "keys" ≠ ofString "nitems" := by decide
  have n2_6 : ofString "keys" ≠ ofString "ncap" := by decide
  have n2_7 : ofString "keys" ≠ ofString "t" := by decide
  have n3_4 : ofString "vals" ≠ ofString "order" := by decide
  have n3_5 : ofString "vals" ≠ ofString "nitems" := by decide
  have n3_6 : ofString "vals" ≠ ofString "ncap" := by decide
  have n3_7 : ofString "vals" ≠ ofString "t" := by decide
  have n4_5 : ofString "order" ≠ ofString "nitems" := by decide
  have n4_6 : ofString "order" ≠ ofString "ncap" := by decide
  have n4_7 : ofString "order" ≠ ofString "t" := by decide
  have n5_6 : ofString "nitems" ≠ ofString "ncap" := by decide
  have n5_7 : ofString "nitems" ≠ ofString "t" := by decide
  have n6_7 : ofString "ncap" ≠ ofString "t" := by decide
  let s1 := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have t1 : state.locals.lookup (ofString "t") = some (.val (.word table)) := by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7] using tableLocal
  have saved1 : state.locals.lookup (ofString "cap") = state.locals.lookup (ofString "cap") := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run1 := fun continuation => evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity continuation t1 domain16 cell16
  let s2 := setVarHOLFinite (ofString "stride") (.val (.word stride)) s1
  have t2 : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7] using tableLocal
  have saved2 : s1.locals.lookup (ofString "stride") = state.locals.lookup (ofString "stride") := by simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run2 := fun continuation => evaluate_header_load_scope s1 (ofString "stride") (ofString "t") table 8 stride continuation t2 domain8 cell8
  let s3 := setVarHOLFinite (ofString "keys") (.val (.word keys)) s2
  have t3 : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by simpa [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7] using tableLocal
  have saved3 : s2.locals.lookup (ofString "keys") = state.locals.lookup (ofString "keys") := by simp [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run3 := fun continuation => evaluate_header_load_scope s2 (ofString "keys") (ofString "t") table 32 keys continuation t3 domain32 cell32
  let s4 := setVarHOLFinite (ofString "vals") (.val (.word values)) s3
  have t4 : s3.locals.lookup (ofString "t") = some (.val (.word table)) := by simpa [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7] using tableLocal
  have saved4 : s3.locals.lookup (ofString "vals") = state.locals.lookup (ofString "vals") := by simp [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run4 := fun continuation => evaluate_header_load_scope s3 (ofString "vals") (ofString "t") table 40 values continuation t4 domain40 cell40
  let s5 := setVarHOLFinite (ofString "order") (.val (.word order)) s4
  have t5 : s4.locals.lookup (ofString "t") = some (.val (.word table)) := by simpa [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7] using tableLocal
  have saved5 : s4.locals.lookup (ofString "order") = state.locals.lookup (ofString "order") := by simp [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run5 := fun continuation => evaluate_header_load_scope s4 (ofString "order") (ofString "t") table 56 order continuation t5 domain56 cell56
  let s6 := setVarHOLFinite (ofString "nitems") (.val (.word count)) s5
  have t6 : s5.locals.lookup (ofString "t") = some (.val (.word table)) := by simpa [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7] using tableLocal
  have saved6 : s5.locals.lookup (ofString "nitems") = state.locals.lookup (ofString "nitems") := by simp [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run6 := fun continuation => evaluate_header_load_scope s5 (ofString "nitems") (ofString "t") table 24 count continuation t6 domain24 cell24
  let s7 := setVarHOLFinite (ofString "ncap") (.val (.word (capacity * 2))) s6
  have capBinding : s6.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by simp [s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have saved7 : s6.locals.lookup (ofString "ncap") = state.locals.lookup (ofString "ncap") := by simp [s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  have run7 : ∀ continuation, evaluateHOLFiniteState s6
      (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"),.const 2]) continuation) =
      (let output := evaluateHOLFiniteState s7 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (ofString "ncap",s6.locals.lookup (ofString "ncap")))})) := by
    intro continuation
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [eval_htabGrow_doubled_capacity s6 capacity capBinding]
    dsimp only
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capacity * 2)))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
    rw [if_pos shapeOk]
  refine ⟨s7,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · intro continuation
    unfold hashGrowHeaderLoads
    rw [run1]
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
    simp only [restoreGrowthLocals,saved1,saved2,saved3,saved4,saved5,saved6,saved7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · simp [s7,s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n2_3,n2_4,n2_5,n2_6,n2_7,n3_4,n3_5,n3_6,n3_7,n4_5,n4_6,n4_7,n5_6,n5_7,n6_7,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n6_7]
  · intro name outside
    have d0 : ofString "cap" ≠ name := by intro same; apply outside; simp [← same]
    have d1 : ofString "stride" ≠ name := by intro same; apply outside; simp [← same]
    have d2 : ofString "keys" ≠ name := by intro same; apply outside; simp [← same]
    have d3 : ofString "vals" ≠ name := by intro same; apply outside; simp [← same]
    have d4 : ofString "order" ≠ name := by intro same; apply outside; simp [← same]
    have d5 : ofString "nitems" ≠ name := by intro same; apply outside; simp [← same]
    have d6 : ofString "ncap" ≠ name := by intro same; apply outside; simp [← same]
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,d0,d1,d2,d3,d4,d5,d6]

#print axioms source_htabGrow_header_prefix
#print axioms evaluate_htabGrow_header_loads
end InitECandidate.Runtime
