import InitECandidate.Runtime.PanCallCostPlan
import InitECandidate.Runtime.PanExternalCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Size-aware statement traces. Recursive control rules expose every guard
expression and only the statements on the executed branch. `Seq` is structural
composition: it emits no event of its own (no native operation), so actual
association never changes cost. -/
inductive StatementRun {F : Type} : PanSemStateFiniteExact 64 F → ProgHOL 64 →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List WorkEvent → Prop where
  | skip (s) : StatementRun s .skip none s [.statement]
  | seqNext {s first middle second r post left right}
      (one : StatementRun s first none middle left)
      (two : StatementRun middle second r post right) :
      StatementRun s (.seq first second) r post (left ++ right)
  | seqStop {s first second r post left} (terminal : r ≠ none)
      (one : StatementRun s first r post left) :
      StatementRun s (.seq first second) r post left
  | iteYes {s condition yes no value guardEvents r post bodyEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0)
      (body : StatementRun s yes r post bodyEvents) :
      StatementRun s (.ite condition yes no) r post
        (.statement :: (guardEvents ++ bodyEvents))
  | iteNo {s condition yes no guardEvents r post bodyEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents)
      (body : StatementRun s no r post bodyEvents) :
      StatementRun s (.ite condition yes no) r post
        (.statement :: (guardEvents ++ bodyEvents))

  | breakStmt (s) : StatementRun s .break (some .break) s [.statement]
  | continueStmt (s) : StatementRun s .continue (some .continue) s [.statement]
  | whileFalse {s condition body guardEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents) :
      StatementRun s (.while condition body) none s (.statement :: guardEvents)
  | whileNext {s condition body value guardEvents middle r post bodyEvents restEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun (decClockHOLFinite s) body none middle bodyEvents)
      (rest : StatementRun middle (.while condition body) r post restEvents) :
      StatementRun s (.while condition body) r post
        (.statement :: (guardEvents ++ bodyEvents ++ restEvents))
  | whileContinue {s condition body value guardEvents middle r post bodyEvents restEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun (decClockHOLFinite s) body (some .continue) middle bodyEvents)
      (rest : StatementRun middle (.while condition body) r post restEvents) :
      StatementRun s (.while condition body) r post
        (.statement :: (guardEvents ++ bodyEvents ++ restEvents))
  | whileBreak {s condition body value guardEvents post bodyEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun (decClockHOLFinite s) body (some .break) post bodyEvents) :
      StatementRun s (.while condition body) none post
        (.statement :: (guardEvents ++ bodyEvents))
  | whileTimeout {s condition body value guardEvents}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock = 0) :
      StatementRun s (.while condition body) (some .timeOut) (emptyLocalsHOLFinite s)
        (.statement :: guardEvents)
  | whileMissingGuard {s condition body guardEvents}
      (guard : CostedExpressionRun s condition none guardEvents) :
      StatementRun s (.while condition body) (some .error) s (.statement :: guardEvents)

  | whilePropagate {s condition body value guardEvents post bodyEvents result}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (notBreak : result ≠ .break) (notContinue : result ≠ .continue)
      (one : StatementRun (decClockHOLFinite s) body (some result) post bodyEvents) :
      StatementRun s (.while condition body) (some result) post
        (.statement :: (guardEvents ++ bodyEvents))

  | assignValue {s kind name expression value events}
      (expr : CostedExpressionRun s expression (some value) events)
      (valid : isValidValueHOLFinite s kind name value = true) :
      StatementRun s (.assign kind name expression) none (setKvarHOLFinite kind name value s)
        (.statement :: (events ++ .copy (flattenHOL value).length ::
          globalEvents kind (flattenHOL value).length))
  | assignInvalid {s kind name expression value events}
      (expr : CostedExpressionRun s expression (some value) events)
      (invalid : isValidValueHOLFinite s kind name value = false) :
      StatementRun s (.assign kind name expression) (some .error) s (.statement :: events)
  | assignFailure {s kind name expression events}
      (expr : CostedExpressionRun s expression none events) :
      StatementRun s (.assign kind name expression) (some .error) s (.statement :: events)
  | returnValue {s expression value events}
      (expr : CostedExpressionRun s expression (some value) events)
      (size : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32) :
      StatementRun s (.return expression) (some (.returned value)) (emptyLocalsHOLFinite s)
        (.statement :: (events ++ [.copy (flattenHOL value).length]))
  | returnOversize {s expression value events}
      (expr : CostedExpressionRun s expression (some value) events)
      (size : ¬ sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32) :
      StatementRun s (.return expression) (some .error) s (.statement :: events)
  | returnFailure {s expression events}
      (expr : CostedExpressionRun s expression none events) :
      StatementRun s (.return expression) (some .error) s (.statement :: events)

  | raiseValue {s exceptionId expression value events shape}
      (expr : CostedExpressionRun s expression (some value) events)
      (declared : s.eshapes.lookup exceptionId = some shape)
      (shapeMatches : shapeOfHOLExact value = shape)
      (size : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32) :
      StatementRun s (.raise exceptionId expression) (some (.exception exceptionId value))
        (emptyLocalsHOLFinite s) (.statement :: (events ++ [.copy (flattenHOL value).length]))
  | raiseFailure {s exceptionId expression events}
      (expr : CostedExpressionRun s expression none events) :
      StatementRun s (.raise exceptionId expression) (some .error) s (.statement :: events)

  | storeValue {s destination source address value memory addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source (some value) valueEvents)
      (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some memory) :
      StatementRun s (.store destination source) none { s with memory := memory }
        (.statement :: (addressEvents ++ valueEvents ++ [.memory (flattenHOL value).length]))
  | storeRejected {s destination source address value addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source (some value) valueEvents)
      (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = none) :
      StatementRun s (.store destination source) (some .error) s
        (.statement :: (addressEvents ++ valueEvents ++ [.memory (flattenHOL value).length]))
  | storeSourceFailure {s destination source address addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source none valueEvents) :
      StatementRun s (.store destination source) (some .error) s
        (.statement :: (addressEvents ++ valueEvents))
  | storeAddressFailure {s destination source addressEvents}
      (dst : CostedExpressionRun s destination none addressEvents) :
      StatementRun s (.store destination source) (some .error) s (.statement :: addressEvents)

  | store32Value {s destination source address value memory addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
      (write : @panMemStore32HOL 64 _ s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
        (BitVec.ofNat 32 value.toNat) = some memory) :
      StatementRun s (.store32 destination source) none { s with memory := memory }
        (.statement :: (addressEvents ++ valueEvents ++ [.memory 1]))

  | store32Rejected {s destination source address value addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
      (write : @panMemStore32HOL 64 _ s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
        (BitVec.ofNat 32 value.toNat) = none) :
      StatementRun s (.store32 destination source) (some .error) s
        (.statement :: (addressEvents ++ valueEvents ++ [.memory 1]))

  | storeByteValue {s destination source address value memory addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
      (write : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
        (BitVec.ofNat 8 value.toNat) = some memory) :
      StatementRun s (.storeByte destination source) none { s with memory := memory }
        (.statement :: (addressEvents ++ valueEvents ++ [.memory 1]))

  | storeByteRejected {s destination source address value addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
      (write : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
        (BitVec.ofNat 8 value.toNat) = none) :
      StatementRun s (.storeByte destination source) (some .error) s
        (.statement :: (addressEvents ++ valueEvents ++ [.memory 1]))

  | declareValue {s name shape initializer body value initEvents bodyEvents result post}
      (init : CostedExpressionRun s initializer (some value) initEvents)
      (shapeMatch : shapeEqHOL shape (shapeOfHOLExact value) = true)
      (bodyRun : StatementRun (setVarHOLFinite name value s) body result post bodyEvents) :
      StatementRun s (.dec name shape initializer body) result
        { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
        (.statement :: (initEvents ++ [.copy (flattenHOL value).length, .frame 1] ++
          bodyEvents ++ [.copy (((s.locals.lookup name).map
            (fun previous => (flattenHOL previous).length)).getD 0)]))
  | declareMismatch {s name shape initializer body value initEvents}
      (init : CostedExpressionRun s initializer (some value) initEvents)
      (mismatch : shapeEqHOL shape (shapeOfHOLExact value) = false) :
      StatementRun s (.dec name shape initializer body) (some .error) s
        (.statement :: initEvents)
  | declareFailure {s name shape initializer body initEvents}
      (init : CostedExpressionRun s initializer none initEvents) :
      StatementRun s (.dec name shape initializer body) (some .error) s
        (.statement :: initEvents)

  | callDone {s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents result post}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock ≠ 0)
      (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
      (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
      StatementRun s (.call info function arguments) result post
        (.statement :: (expressionListEvents s arguments ++
          [.copy (values.flatMap flattenHOL).length, .frame values.length,
            .frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ bodyEvents ++
          [.copy (callPayloadWords bodyResult)] ++ callGlobalEvents s info))
  | callHandler {s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents handlerEntry handlerProgram handlerEvents result post}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock ≠ 0)
      (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
      (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler handlerEntry handlerProgram)
      (handlerRun : StatementRun handlerEntry handlerProgram result post handlerEvents) :
      StatementRun s (.call info function arguments) result post
        (.statement :: (expressionListEvents s arguments ++
          [.copy (values.flatMap flattenHOL).length, .frame values.length,
            .frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ bodyEvents ++
          [.copy (callPayloadWords bodyResult)] ++ handlerEvents))
  | callArgumentsFailure {s info function arguments}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = none) :
      StatementRun s (.call info function arguments) (some .error) s
        (.statement :: expressionListEvents s arguments)
  | callLookupFailure {s info function arguments values}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = none) :
      StatementRun s (.call info function arguments) (some .error) s
        (.statement :: expressionListEvents s arguments)
  | callTimeout {s info function arguments values body callee returnShape}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock = 0) :
      StatementRun s (.call info function arguments) (some .timeOut) (emptyLocalsHOLFinite s)
        (.statement :: (expressionListEvents s arguments ++
          [.frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ callGlobalEvents s info))

  | declareCallReturn {s name shape function arguments continuation values body callee returnShape
      value bodyPost bodyEvents continuationEvents result post}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock ≠ 0)
      (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body
        (some (.returned value)) bodyPost bodyEvents)
      (shapeMatch : (shapeEqHOL (shapeOfHOLExact value) shape &&
        shapeEqHOL (shapeOfHOLExact value) returnShape) = true)
      (continuationRun : StatementRun
        (setVarHOLFinite name value { bodyPost with locals := s.locals })
        continuation result post continuationEvents) :
      StatementRun s (.decCall name shape function arguments continuation) result
        { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
        (.statement :: (expressionListEvents s arguments ++
          [.copy (values.flatMap flattenHOL).length, .frame values.length,
            .frame (sizeOfShapeWithContextHOL s.structs shape)] ++ bodyEvents ++
          [.copy (flattenHOL value).length] ++ continuationEvents ++
          [.copy (((s.locals.lookup name).map (fun old => (flattenHOL old).length)).getD 0)]))

  | declareCallArgumentsFailure {s name shape function arguments continuation}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = none) :
      StatementRun s (.decCall name shape function arguments continuation) (some .error) s
        (.statement :: expressionListEvents s arguments)
  | declareCallLookupFailure {s name shape function arguments continuation values}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = none) :
      StatementRun s (.decCall name shape function arguments continuation) (some .error) s
        (.statement :: expressionListEvents s arguments)
  | declareCallTimeout {s name shape function arguments continuation values body callee returnShape}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock = 0) :
      StatementRun s (.decCall name shape function arguments continuation)
        (some .timeOut) (emptyLocalsHOLFinite s) (.statement :: (expressionListEvents s arguments ++
          [.frame (sizeOfShapeWithContextHOL s.structs shape)]))
  | declareCallRejectedReturn {s name shape function arguments continuation values body callee returnShape
      value bodyPost bodyEvents}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock ≠ 0)
      (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body
        (some (.returned value)) bodyPost bodyEvents)
      (shapeMismatch : (shapeEqHOL (shapeOfHOLExact value) shape &&
        shapeEqHOL (shapeOfHOLExact value) returnShape) = false) :
      StatementRun s (.decCall name shape function arguments continuation) (some .error) bodyPost
        (.statement :: (expressionListEvents s arguments ++
          [.copy (values.flatMap flattenHOL).length, .frame values.length,
            .frame (sizeOfShapeWithContextHOL s.structs shape)] ++ bodyEvents))
  | declareCallStopped {s name shape function arguments continuation values body callee returnShape
      bodyResult bodyPost bodyEvents}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
      (clock : s.clock ≠ 0)
      (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
      (terminal : ∀ value, bodyResult ≠ some (.returned value)) :
      StatementRun s (.decCall name shape function arguments continuation)
        (declareCallStopPlan bodyResult bodyPost).1 (declareCallStopPlan bodyResult bodyPost).2
        (.statement :: (expressionListEvents s arguments ++
          [.copy (values.flatMap flattenHOL).length, .frame values.length,
            .frame (sizeOfShapeWithContextHOL s.structs shape)] ++ bodyEvents ++
          [.copy (callPayloadWords bodyResult)]))

  | tickStep {s} (clock : s.clock ≠ 0) :
      StatementRun s .tick none (decClockHOLFinite s) [.statement]
  | tickTimeout {s} (clock : s.clock = 0) :
      StatementRun s .tick (some .timeOut) (emptyLocalsHOLFinite s) [.statement]
  | annotation {s tag text} : StatementRun s (.annot tag text) none s [.statement]
  | iteInvalidGuard {s condition yes no value events}
      (guard : CostedExpressionRun s condition value events)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.ite condition yes no) (some .error) s (.statement :: events)
  | whileInvalidGuard {s condition body value events}
      (guard : CostedExpressionRun s condition value events)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.while condition body) (some .error) s (.statement :: events)

  | storeInvalidAddress {s destination source value events}
      (dst : CostedExpressionRun s destination value events)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.store destination source) (some .error) s (.statement :: events)

  | store32InvalidAddress {s destination source value events}
      (dst : CostedExpressionRun s destination value events)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.store32 destination source) (some .error) s (.statement :: events)

  | storeByteInvalidAddress {s destination source value events}
      (dst : CostedExpressionRun s destination value events)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.storeByte destination source) (some .error) s (.statement :: events)

  | store32InvalidValue {s destination source address value addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source value valueEvents)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.store32 destination source) (some .error) s
        (.statement :: (addressEvents ++ valueEvents))

  | storeByteInvalidValue {s destination source address value addressEvents valueEvents}
      (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
      (src : CostedExpressionRun s source value valueEvents)
      (invalid : ∀ word, value ≠ some (.val (.word word))) :
      StatementRun s (.storeByte destination source) (some .error) s
        (.statement :: (addressEvents ++ valueEvents))

  | primitiveValue {s name operator arguments values value}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (operation : panPrimopHOLExact operator values = some value)
      (valid : isValidValueHOLFinite s .local name value = true) :
      StatementRun s (.primitive name operator arguments) none (setVarHOLFinite name value s)
        (.statement :: (expressionListEvents s arguments ++ [.scalar 1] ++ [.copy (flattenHOL value).length]))

  | primitiveInvalid {s name operator arguments values value}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (operation : panPrimopHOLExact operator values = some value)
      (valid : isValidValueHOLFinite s .local name value = false) :
      StatementRun s (.primitive name operator arguments) (some .error) s
        (.statement :: (expressionListEvents s arguments ++ [.scalar 1]))

  | primitiveRejected {s name operator arguments values}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = some values)
      (operation : panPrimopHOLExact operator values = none) :
      StatementRun s (.primitive name operator arguments) (some .error) s
        (.statement :: (expressionListEvents s arguments ++ [.scalar 1]))

  | primitiveArgumentsFailure {s name operator arguments}
      (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        arguments = none) :
      StatementRun s (.primitive name operator arguments) (some .error) s
        (.statement :: expressionListEvents s arguments)

  | raiseUndeclared {s exceptionId expression value events}
      (expr : CostedExpressionRun s expression value events)
      (missing : s.eshapes.lookup exceptionId = none) :
      StatementRun s (.raise exceptionId expression) (some .error) s (.statement :: events)
  | raiseRejectedValue {s exceptionId expression value events shape}
      (expr : CostedExpressionRun s expression (some value) events)
      (declared : s.eshapes.lookup exceptionId = some shape)
      (invalid : ¬ (shapeOfHOLExact value = shape ∧
        sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32)) :
      StatementRun s (.raise exceptionId expression) (some .error) s (.statement :: events)

  /-- Atomic semantic boundary: external effects have no recursive source body.
  Expression and transfer work is fixed by the canonical source cost functions. -/
  | external {s function configuration configurationLength array arrayLength result post}
      (run : evaluateHOLFiniteState s
        (.extCall function configuration configurationLength array arrayLength) = (result, post)) :
      StatementRun s (.extCall function configuration configurationLength array arrayLength)
        result post (externalEvents s function configuration configurationLength array arrayLength)
  | sharedLoad {s operator kind name address result post}
      (run : evaluateHOLFiniteState s (.shMemLoad operator kind name address) = (result, post)) :
      StatementRun s (.shMemLoad operator kind name address) result post
        (sharedLoadEvents s kind name address)
  | sharedStore {s operator address value result post}
      (run : evaluateHOLFiniteState s (.shMemStore operator address value) = (result, post)) :
      StatementRun s (.shMemStore operator address value) result post
        (sharedStoreEvents s address value)

theorem StatementRun.sound {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) : evaluateHOLFiniteState s p = (r, post) := by
  induction run with
  | skip s => exact evaluateHOLFiniteState_skip s
  | seqNext one two ihOne ihTwo =>
    rw [evaluateHOLFiniteState_seq]
    dsimp only
    rw [fixClockHOLFinite_evaluateState, ihOne]
    exact ihTwo
  | @seqStop state first second result final left terminal one ih =>
    rw [evaluateHOLFiniteState_seq]
    dsimp only
    rw [fixClockHOLFinite_evaluateState, ih]
    cases result <;> simp_all
  | @iteYes state condition yes no value guardEvents result final bodyEvents guard nonzero body ih =>
    have evalGuard := guard.sound
    unfold expressionValue at evalGuard
    rw [evaluateHOLFiniteState_ite, evalGuard]
    have zero : value ≠ (0#64) := nonzero
    simpa [zero] using ih
  | iteNo guard body ih =>
    have evalGuard := guard.sound
    unfold expressionValue at evalGuard
    rw [evaluateHOLFiniteState_ite, evalGuard]
    simpa using ih

  | breakStmt s => exact evaluateHOLFiniteState_break s
  | continueStmt s => exact evaluateHOLFiniteState_continue s
  | whileFalse guard =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    simp only [evalHOLFinite_eq_toExact, hg]
    simp
  | whileNext guard nonzero clock one rest ihOne ihRest =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock, ihOne]
    exact ihRest
  | whileContinue guard nonzero clock one rest ihOne ihRest =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock, ihOne]
    exact ihRest
  | whileBreak guard nonzero clock one ihOne =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock, ihOne]
  | whileTimeout guard nonzero clock =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock]
  | whileMissingGuard guard =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    simp only [evalHOLFinite_eq_toExact, hg]

  | whilePropagate guard nonzero clock notBreak notContinue one ihOne =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp only [evalHOLFinite_eq_toExact, hg]
    simp [nonzero, clock, ihOne, notBreak, notContinue]

  | assignValue expr valid =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_assign, he]
    simp only [valid, ↓reduceIte]
  | assignInvalid expr invalid =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_assign, he]
    simp only [invalid, Bool.false_eq_true, ↓reduceIte]
  | assignFailure expr =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_assign, he]
  | returnValue expr size =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_return, he]
    simp [size]
  | returnOversize expr size =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_return, he]
    simp [size]
  | returnFailure expr =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_return, he]

  | raiseValue expr declared shapeMatches size =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_raise, he, declared]
    simp only [shapeMatches, size, and_self, ↓reduceIte]
    simp_all
  | raiseFailure expr =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_raise, he]
    split <;> simp_all

  | storeValue dst src write =>
    have hd := dst.sound
    unfold expressionValue at hd
    have hs := src.sound
    unfold expressionValue at hs
    rw [evaluateHOLFiniteState_store, hd, hs]
    simp only [write]
  | storeRejected dst src write =>
    have hd := dst.sound
    unfold expressionValue at hd
    have hs := src.sound
    unfold expressionValue at hs
    rw [evaluateHOLFiniteState_store, hd, hs]
    simp only [write]
  | storeSourceFailure dst src =>
    have hd := dst.sound
    unfold expressionValue at hd
    have hs := src.sound
    unfold expressionValue at hs
    rw [evaluateHOLFiniteState_store, hd, hs]
  | storeAddressFailure dst =>
    have hd := dst.sound
    unfold expressionValue at hd
    rw [evaluateHOLFiniteState_store, hd]

  | store32Value dst src write =>
    have hd := dst.sound
    have hs := src.sound
    unfold expressionValue at hd hs
    rw [evaluateHOLFiniteState_store32, hd, hs]
    simp only [write]
  | store32Rejected dst src write =>
    have hd := dst.sound
    have hs := src.sound
    unfold expressionValue at hd hs
    rw [evaluateHOLFiniteState_store32, hd, hs]
    simp only [write]
  | storeByteValue dst src write =>
    have hd := dst.sound
    have hs := src.sound
    unfold expressionValue at hd hs
    rw [evaluateHOLFiniteState_storeByte, hd, hs]
    simp only [write]
  | storeByteRejected dst src write =>
    have hd := dst.sound
    have hs := src.sound
    unfold expressionValue at hd hs
    rw [evaluateHOLFiniteState_storeByte, hd, hs]
    simp only [write]

  | declareValue init shapeMatch bodyRun ih =>
    have he := init.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_dec_total]
    simp only [he, shapeMatch, ↓reduceIte, ih]
  | declareMismatch init mismatch =>
    have he := init.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_dec_total]
    simp only [he, mismatch, Bool.false_eq_true, ↓reduceIte]
  | declareFailure init =>
    have he := init.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_dec_total]
    simp only [he]

  | @callDone state info function arguments values body callee returnShape bodyResult bodyPost bodyEvents result post args lookup clock bodyRun plan ih =>
    have hc := evaluate_call_cost_plan _ info _ _ _ _ _ _ _ _ args lookup clock ih
    simpa only [plan, evaluateCallCostPlan] using hc
  | @callHandler state info function arguments values body callee returnShape bodyResult bodyPost bodyEvents handlerEntry handlerProgram handlerEvents result post args lookup clock bodyRun plan handlerRun ihBody ihHandler =>
    have hc := evaluate_call_cost_plan _ info _ _ _ _ _ _ _ _ args lookup clock ihBody
    simpa only [plan, evaluateCallCostPlan, ihHandler] using hc
  | callArgumentsFailure args =>
    rw [evaluateHOLFiniteState_call]
    simp only [args]
  | callLookupFailure args lookup =>
    rw [evaluateHOLFiniteState_call]
    simp only [args, lookup]
  | callTimeout args lookup clock =>
    rw [evaluateHOLFiniteState_call]
    simp only [args, lookup, clock, ↓reduceIte]

  | declareCallReturn args lookup clock bodyRun shapeMatch continuationRun ihBody ihContinuation =>
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [args, lookup, clock, ↓reduceIte, fixClockHOLFinite_evaluateState]
    simp only [ihBody, shapeMatch, ↓reduceIte, ihContinuation]

  | declareCallArgumentsFailure args =>
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [args]
  | declareCallLookupFailure args lookup =>
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [args, lookup]
  | declareCallTimeout args lookup clock =>
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [args, lookup, clock, ↓reduceIte]
  | declareCallRejectedReturn args lookup clock bodyRun shapeMismatch ihBody =>
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [args, lookup, clock, ↓reduceIte, fixClockHOLFinite_evaluateState]
    simp only [ihBody, shapeMismatch, Bool.false_eq_true, ↓reduceIte]
  | @declareCallStopped state name shape function arguments continuation values body callee returnShape bodyResult bodyPost bodyEvents args lookup clock bodyRun terminal ihBody =>
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [args, lookup, clock, ↓reduceIte, fixClockHOLFinite_evaluateState]
    simp only [ihBody]
    cases bodyResult with
    | none => rfl
    | some result =>
      cases result <;> try rfl
      exact False.elim (terminal _ rfl)


  | tickStep clock => rw [evaluateHOLFiniteState_tick]; simp only [clock, ↓reduceIte]
  | tickTimeout clock => rw [evaluateHOLFiniteState_tick]; simp only [clock, ↓reduceIte]
  | annotation => exact evaluateHOLFiniteState_annot _ _ _
  | @iteInvalidGuard state condition yes no value events guard invalid =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_ite]
    rw [hg]
    cases value with
    | none => rfl
    | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val word => cases word; exact False.elim (invalid _ rfl)
  | @whileInvalidGuard state condition body value events guard invalid =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    simp only [evalHOLFinite_eq_toExact, hg]
  | @storeInvalidAddress state destination source value events dst invalid =>
    have hd := dst.sound
    unfold expressionValue at hd
    rw [evaluateHOLFiniteState_store, hd]
    cases value with
    | none => rfl
    | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val word => cases word; exact False.elim (invalid _ rfl)
  | @store32InvalidAddress state destination source value events dst invalid =>
    have hd := dst.sound
    unfold expressionValue at hd
    rw [evaluateHOLFiniteState_store32, hd]
    cases value with
    | none => rfl
    | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val word => cases word; exact False.elim (invalid _ rfl)
  | @storeByteInvalidAddress state destination source value events dst invalid =>
    have hd := dst.sound
    unfold expressionValue at hd
    rw [evaluateHOLFiniteState_storeByte, hd]
    cases value with
    | none => rfl
    | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val word => cases word; exact False.elim (invalid _ rfl)
  | @store32InvalidValue state destination source address value addressEvents valueEvents dst src invalid =>
    have hd := dst.sound
    have hs := src.sound
    unfold expressionValue at hd hs
    rw [evaluateHOLFiniteState_store32, hd, hs]
    cases value with
    | none => rfl
    | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val word => cases word; exact False.elim (invalid _ rfl)
  | @storeByteInvalidValue state destination source address value addressEvents valueEvents dst src invalid =>
    have hd := dst.sound
    have hs := src.sound
    unfold expressionValue at hd hs
    rw [evaluateHOLFiniteState_storeByte, hd, hs]
    cases value with
    | none => rfl
    | some value =>
      cases value with
      | rStruct fields => rfl
      | nStruct name fields => rfl
      | val word => cases word; exact False.elim (invalid _ rfl)

  | primitiveValue args operation valid =>
    rw [evalListHOLFinite_eq_toExact] at args
    rw [evaluateHOLFiniteState_primitive]
    simp only [args, operation, valid, Bool.false_eq_true, ↓reduceIte]
  | primitiveInvalid args operation valid =>
    rw [evalListHOLFinite_eq_toExact] at args
    rw [evaluateHOLFiniteState_primitive]
    simp only [args, operation, valid, Bool.false_eq_true, ↓reduceIte]
  | primitiveRejected args operation =>
    rw [evalListHOLFinite_eq_toExact] at args
    rw [evaluateHOLFiniteState_primitive]
    simp only [args, operation]
  | primitiveArgumentsFailure args =>
    rw [evalListHOLFinite_eq_toExact] at args
    rw [evaluateHOLFiniteState_primitive]
    simp only [args]

  | raiseUndeclared expr missing =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_raise]
    simp only [he, missing]
  | raiseRejectedValue expr declared invalid =>
    have he := expr.sound
    unfold expressionValue at he
    rw [evaluateHOLFiniteState_raise]
    simp only [he, declared, invalid, ↓reduceIte]

  | external run => exact run
  | sharedLoad run => exact run
  | sharedStore run => exact run

#print axioms StatementRun.sound
end InitECandidate.Runtime.FineCost
