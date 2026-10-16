import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGrowRehashBody : ProgHOL 64 :=
  .dec (ofString "i") .one (.load .one (hashOrderAddress (ofString "order") (ofString "k")))
    (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
      [.var .local (ofString "t"),
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .load .one (hashOrderAddress (ofString "vals") (ofString "i"))])
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1])))

def hashGrowRehashLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "k")) (.var .local (ofString "nitems"))) hashGrowRehashBody

/-- The ranked rehash loop is the literal original growth loop, including
its signed comparison, order lookup, insertion call and counter update. -/
theorem source_htabGrow_rehash_scope :
    sourceFindLocalScope (ofString "k") (sourceFunctionBody Guest.guestFn_htab_grow) =
      some (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0)))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual growth doubling expression reads the old capacity local. -/
theorem eval_htabGrow_doubled_capacity {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity : BitVec 64)
    (binding : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.panop .mul [.var .local (ofString "cap"),.const 2]) = some (.val (.word (capacity * 2))) := by
  simp [evalHOLExact,evalListHOLExact,binding,panOpHOL,valueIsWord,valueWord]

#print axioms source_htabGrow_rehash_scope
#print axioms eval_htabGrow_doubled_capacity
end InitECandidate.Runtime
