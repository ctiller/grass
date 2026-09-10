import Grass.ISA.Wasm.Module

/-!
Checked source-site and imported-host invocation construction. The store is a
snapshot of the selected runtime, not a second memory model. The checker binds
the reached function through its owning module to the original emitted source.
It proves local resolution and argument typing, not global store validity,
module validation, runtime instantiation adequacy, or provider correctness.
-/
namespace Grass.ISA.Wasm

structure ModuleInstance where
  artifact : Artifact
  functionAddrs : List FuncAddr

inductive FunctionInstance where
  | host (type : FuncType) (id : HostId)
  | defined (module : ModuleAddr) (definition : Nat)
deriving DecidableEq, Repr

structure Store where
  modules : List ModuleInstance
  functions : List FunctionInstance

/-- Current activation of a defined function. Stack top is the list head.
Caller activations and host side effects belong to the later execution adapter. -/
structure State where
  function : FuncAddr
  pc : Nat
  locals : List Value
  stack : List Value
deriving DecidableEq, Repr

inductive ResolveError where
  | missingFunction | notDefined | missingModule | missingDefinition
  | callerBindingMismatch | localTypesMismatch | noInstruction | notCall
  | notImport | missingCallee | notHost | signatureMismatch | missingArguments
  | argumentTypesMismatch
deriving DecidableEq, Repr

/-- Site identity includes the exact store and activation, never just an index. -/
structure Site (store : Store) (before : State) where
  private mk ::
  moduleAddr : ModuleAddr
  definitionIndex : Nat
  callerLookup : store.functions[before.function.index]? =
    some (.defined moduleAddr definitionIndex)
  moduleInst : ModuleInstance
  moduleLookup : store.modules[moduleAddr.index]? = some moduleInst
  definition : Function
  definitionLookup : moduleInst.artifact.source.functions[definitionIndex]? = some definition
  callerBinding : moduleInst.functionAddrs[moduleInst.artifact.source.imports.length +
    definitionIndex]? = some before.function
  localTypes : before.locals.map Value.type = definition.type.params ++ definition.locals
  instruction : Instruction
  instructionLookup : definition.body[before.pc]? = some instruction

def Site.check (store : Store) (before : State) : Except ResolveError (Site store before) := do
  match hc : store.functions[before.function.index]? with
  | none => throw .missingFunction
  | some (.host _ _) => throw .notDefined
  | some (.defined moduleAddr definitionIndex) =>
    match hm : store.modules[moduleAddr.index]? with
    | none => throw .missingModule
    | some moduleInst =>
      match hd : moduleInst.artifact.source.functions[definitionIndex]? with
      | none => throw .missingDefinition
      | some definition =>
        if hb : moduleInst.functionAddrs[moduleInst.artifact.source.imports.length +
            definitionIndex]? = some before.function then
          if hl : before.locals.map Value.type = definition.type.params ++ definition.locals then
            match hi : definition.body[before.pc]? with
            | none => throw .noInstruction
            | some instruction =>
              return ⟨moduleAddr, definitionIndex, hc, moduleInst, hm,
                definition, hd, hb, hl, instruction, hi⟩
          else throw .localTypesMismatch
        else throw .callerBindingMismatch

/-- Checked imported-invocation inputs, before any host service or return. Arguments use
parameter order; continuation retains the caller with those arguments removed.
Import names record the exact source declaration; they do not attest a provider.
This pure receipt is reusable for the same snapshot, not a fresh occurrence or
single-use capability. The provider handoff must mint and bind its own occurrence
through the actual protocol transition before it can authorize completion. -/
structure HostInvocation (store : Store) (before : State) where
  private mk ::
  site : Site store before
  functionIndex : Nat
  isCall : site.instruction = .call functionIndex
  importDecl : Import
  importLookup : site.moduleInst.artifact.source.imports[functionIndex]? = some importDecl
  callee : FuncAddr
  calleeLookup : site.moduleInst.functionAddrs[functionIndex]? = some callee
  hostId : HostId
  hostLookup : store.functions[callee.index]? = some (.host importDecl.type hostId)
  enoughArguments : importDecl.type.params.length ≤ before.stack.length
  argumentTypes : ((before.stack.take importDecl.type.params.length).reverse.map Value.type) =
    importDecl.type.params

def HostInvocation.arguments {store : Store} {before : State}
    (call : HostInvocation store before) : List Value :=
  (before.stack.take call.importDecl.type.params.length).reverse

def HostInvocation.continuation {store : Store} {before : State}
    (call : HostInvocation store before) : State :=
  { before with pc := before.pc + 1, stack := before.stack.drop call.importDecl.type.params.length }

def HostInvocation.check (store : Store) (before : State) :
    Except ResolveError (HostInvocation store before) := do
  let site ← Site.check store before
  match hi : site.instruction with
  | .call index =>
    match hd : site.moduleInst.artifact.source.imports[index]? with
    | none => throw .notImport
    | some imp =>
      match ha : site.moduleInst.functionAddrs[index]? with
      | none => throw .missingCallee
      | some addr =>
        match hh : store.functions[addr.index]? with
        | none => throw .missingCallee
        | some (.defined _ _) => throw .notHost
        | some (.host type hostId) =>
          if ht : type = imp.type then
            if hn : imp.type.params.length ≤ before.stack.length then
              if hv : ((before.stack.take imp.type.params.length).reverse.map Value.type) =
                  imp.type.params then
                return ⟨site, index, hi, imp, hd, addr, ha, hostId, ht ▸ hh, hn, hv⟩
              else throw .argumentTypesMismatch
            else throw .missingArguments
          else throw .signatureMismatch
  | _ => throw .notCall

theorem HostInvocation.arguments_typed {store : Store} {before : State}
    (call : HostInvocation store before) :
    call.arguments.map Value.type = call.importDecl.type.params := call.argumentTypes

theorem HostInvocation.stack_split {store : Store} {before : State}
    (call : HostInvocation store before) :
    call.arguments.reverse ++ call.continuation.stack = before.stack := by
  simp [arguments, continuation]

theorem HostInvocation.continuation_locals {store : Store} {before : State}
    (call : HostInvocation store before) : call.continuation.locals = before.locals := rfl

/-- The source occurrence used for the invocation is an actual CALL in the
original module's function body, not a separately supplied instruction list. -/
theorem HostInvocation.source_call {store : Store} {before : State}
    (call : HostInvocation store before) :
    call.site.definition.body[before.pc]? = some (.call call.functionIndex) := by
  rw [call.site.instructionLookup, call.isCall]

/-- Every receipt retains the full production artifact equation. This theorem
does not replace the future binary-parser/instantiation adequacy theorem. -/
theorem HostInvocation.source_bytes {store : Store} {before : State}
    (call : HostInvocation store before) :
    call.site.moduleInst.artifact.source.encode = some call.site.moduleInst.artifact.bytes :=
  call.site.moduleInst.artifact.emitted

end Grass.ISA.Wasm
