import InitECandidate.Runtime.SourceCostGlobalsRunWhile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Atomic rules of the `pan_globals` statement transfer. A compiled branch
other than the source's ends with a different result than the source run
(`globals_sub_match` on the whole statement). -/

theorem globals_skip (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    GlobalsLe B s .skip none s [.statement] := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [compileProgExactHOL] at target
  cases target
  exact Nat.le_refl _

theorem globals_break (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    GlobalsLe B s .break (some .break) s [.statement] := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [compileProgExactHOL] at target
  cases target
  exact Nat.le_refl _

theorem globals_continue (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    GlobalsLe B s .continue (some .continue) s [.statement] := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [compileProgExactHOL] at target
  cases target
  exact Nat.le_refl _

theorem globals_annotation (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (tag text) :
    GlobalsLe B s (.annot tag text) none s [.statement] := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [compileProgExactHOL] at target
  cases target
  exact Nat.le_refl _

theorem globals_tick (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (r post) :
    GlobalsLe B s .tick r post [.statement] := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [compileProgExactHOL] at target
  cases target <;> exact Nat.le_refl _

theorem globals_storeValue (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {destination source : ExpHOL 64} {address : BitVec 64} {value : ValueHOL 64} {memory}
    {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
    (src : CostedExpressionRun s source (some value) valueEvents)
    (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some memory) :
    GlobalsLe B s (.store destination source) none { s with memory := memory }
      (.statement :: (addressEvents ++ valueEvents ++ [.memory (flattenHOL value).length])) := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.storeValue dst src write) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case storeValue =>
    obtain ⟨_, a⟩ := globals_costed B rel dst (by assumption) ready.1
    obtain ⟨hv, b⟩ := globals_costed B rel src (by assumption) ready.2
    cases hv
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_memory, sharpSourceScore_nil]
    omega
  all_goals cases hr

theorem globals_store32Value (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {destination source : ExpHOL 64} {address value : BitVec 64} {memory}
    {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
    (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
    (write : @panMemStore32HOL 64 _ s.memory s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
      (BitVec.ofNat 32 value.toNat) = some memory) :
    GlobalsLe B s (.store32 destination source) none { s with memory := memory }
      (.statement :: (addressEvents ++ valueEvents ++ [.memory 1])) := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.store32Value dst src write) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case store32Value =>
    obtain ⟨_, a⟩ := globals_costed B rel dst (by assumption) ready.1
    obtain ⟨_, b⟩ := globals_costed B rel src (by assumption) ready.2
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_memory, sharpSourceScore_nil]
    omega
  all_goals cases hr

theorem globals_storeByteValue (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {destination source : ExpHOL 64} {address value : BitVec 64} {memory}
    {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
    (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
    (write : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
      (BitVec.ofNat 8 value.toNat) = some memory) :
    GlobalsLe B s (.storeByte destination source) none { s with memory := memory }
      (.statement :: (addressEvents ++ valueEvents ++ [.memory 1])) := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.storeByteValue dst src write) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case storeByteValue =>
    obtain ⟨_, a⟩ := globals_costed B rel dst (by assumption) ready.1
    obtain ⟨_, b⟩ := globals_costed B rel src (by assumption) ready.2
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_memory, sharpSourceScore_nil]
    omega
  all_goals cases hr

theorem globals_returnValue (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {expression : ExpHOL 64} {value : ValueHOL 64} {events : List WorkEvent}
    (expr : CostedExpressionRun s expression (some value) events)
    (size : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32) :
    GlobalsLe B s (.return expression) (some (.returned value)) (emptyLocalsHOLFinite s)
      (.statement :: (events ++ [.copy (flattenHOL value).length])) := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [globalsReadyProg] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.returnValue expr size) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case returnValue =>
    obtain ⟨hv, a⟩ := globals_costed B rel expr (by assumption) ready
    cases hv
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_copy, sharpSourceScore_nil]
    omega
  all_goals cases hr

theorem globals_raiseValue (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {exceptionId} {expression : ExpHOL 64} {value : ValueHOL 64} {events : List WorkEvent} {shape}
    (expr : CostedExpressionRun s expression (some value) events)
    (declared : s.eshapes.lookup exceptionId = some shape)
    (shapeMatches : shapeOfHOLExact value = shape)
    (size : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32) :
    GlobalsLe B s (.raise exceptionId expression) (some (.exception exceptionId value))
      (emptyLocalsHOLFinite s) (.statement :: (events ++ [.copy (flattenHOL value).length])) := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [globalsReadyProg] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.raiseValue expr declared shapeMatches size) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case raiseValue =>
    obtain ⟨hv, a⟩ := globals_costed B rel expr (by assumption) ready
    cases hv
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_copy, sharpSourceScore_nil]
    omega
  all_goals cases hr

theorem globals_assignLocal (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name} {expression : ExpHOL 64} {value : ValueHOL 64} {events : List WorkEvent}
    (expr : CostedExpressionRun s expression (some value) events)
    (valid : isValidValueHOLFinite s .local name value = true) :
    GlobalsLe B s (.assign .local name expression) none (setKvarHOLFinite .local name value s)
      (.statement :: (events ++ .copy (flattenHOL value).length ::
        globalEvents .local (flattenHOL value).length)) := by
  intro context t rel ok ready code h r' t' ev' target
  simp only [globalsReadyProg] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.assignValue expr valid) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case assignValue =>
    obtain ⟨hv, a⟩ := globals_costed B rel expr (by assumption) ready
    cases hv
    simp only [globalEvents, srcScore_statement, sharpSourceScore_append, srcScore_copy,
      sharpSourceScore_nil]
    omega
  all_goals cases hr

#print axioms globals_storeValue
#print axioms globals_returnValue
#print axioms globals_raiseValue
#print axioms globals_assignLocal
#print axioms globals_tick
end InitECandidate.Runtime.FineCost
