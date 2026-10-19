import InitECandidate.Runtime.ValidateHeadersHeaderStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful actual header-pointer store makes its destination readable
and records the decoded header pointer there. The successful execution,
rather than a separate domain assumption, supplies accessibility. -/
theorem validate_headers_store_content {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs index header : BitVec 64)
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHeader : s.locals.lookup (ofString "h") = some (.val (.word header)))
    (normal : evaluateHOLFiniteState s validateHeadersHeaderStore = (none,post)) :
    post.memaddrs (hs + index * (8#64)) ∧ post.memory (hs + index * (8#64)) = .word header := by
  have dest : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "hs"),.panop .mul [.var .local (ofString "i"),.const 8]]) =
      some (.val (.word (hs + index * (8#64)))) := by
    simp [evalHOLExact,evalListHOLExact,atHs,atIndex,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  unfold validateHeadersHeaderStore at normal
  rw [evaluateHOLFiniteState_store,dest] at normal
  simp only [evalHOLExact,atHeader] at normal
  by_cases accessible : s.memaddrs (hs + index * (8#64))
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at normal
    subst post
    simp [accessible]
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at normal

#print axioms validate_headers_store_content
end InitECandidate.Runtime
