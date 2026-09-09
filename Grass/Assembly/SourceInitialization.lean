import Grass.Assembly.SourceFrame
import Grass.Assembly.Store32

/-!
# Source-derived local initialization

Every `UInt32` local in `SourceFrame.header.locals` becomes one checked `Store32`
input, in declaration order, using the frame's sole derived slot environment.
Resolution is all-or-none.  This module describes the initializer sequence; it
does not splice it into a prologue or claim ISA execution.
-/

namespace Grass.Assembly.SourceInitialization

open Grass.ISA.X86 Grass.Memory

def inputOf (declaration : SourceFrameHeader.Local) : Store32.Input :=
  ⟨declaration.name, BitVec.ofNat 32 declaration.initialValue.toNat⟩

structure Entry where
  private mk ::
  declaration : SourceFrameHeader.Local
  store : Store32.Resolved

private def resolveEntries? (layout : Grass.ABI.Win64.CallFrameLayout)
    (rootOffset : Nat) (env : Store32.SlotEnv) :
    List SourceFrameHeader.Local → Option (List Entry)
  | [] => some []
  | declaration :: rest => do
      let store ← Store32.resolve? layout rootOffset env (inputOf declaration)
      let tail ← resolveEntries? layout rootOffset env rest
      pure (⟨declaration, store⟩ :: tail)

structure Result where
  private mk ::
  frame : SourceFrame.Result
  rootOffset : Nat
  entries : List Entry
  entriesExact : resolveEntries? frame.layout rootOffset
    (SourceStore.slotEnv frame.slots) frame.header.locals = some entries

def resolve? (frame : SourceFrame.Result) (rootOffset : Nat) : Option Result :=
  match exact : resolveEntries? frame.layout rootOffset
      (SourceStore.slotEnv frame.slots) frame.header.locals with
  | none => none
  | some entries => some ⟨frame, rootOffset, entries, exact⟩

theorem resolve?_source {frame : SourceFrame.Result} {rootOffset : Nat} {result : Result}
    (success : resolve? frame rootOffset = some result) :
    result.frame = frame ∧ result.rootOffset = rootOffset := by
  unfold resolve? at success
  split at success <;> try contradiction
  cases success
  exact ⟨rfl, rfl⟩

private theorem resolveEntries?_declarations
    {layout : Grass.ABI.Win64.CallFrameLayout} {rootOffset : Nat}
    {env : Store32.SlotEnv} {locals : List SourceFrameHeader.Local} {entries : List Entry}
    (success : resolveEntries? layout rootOffset env locals = some entries) :
    entries.map Entry.declaration = locals := by
  induction locals generalizing entries with
  | nil => simp [resolveEntries?] at success; cases success; rfl
  | cons declaration rest ih =>
      cases storeExact : Store32.resolve? layout rootOffset env (inputOf declaration) with
      | none => simp [resolveEntries?, storeExact] at success
      | some store =>
          cases tailExact : resolveEntries? layout rootOffset env rest with
          | none => simp [resolveEntries?, storeExact, tailExact] at success
          | some tail =>
              simp [resolveEntries?, storeExact, tailExact] at success
              cases success
              simp [ih tailExact]

theorem Result.declaration_order (result : Result) :
    result.entries.map Entry.declaration = result.frame.header.locals :=
  resolveEntries?_declarations result.entriesExact

theorem Result.count (result : Result) :
    result.entries.length = result.frame.header.locals.length := by
  have order := result.declaration_order
  simpa using congrArg List.length order

private theorem resolveEntries?_member
    {layout : Grass.ABI.Win64.CallFrameLayout} {rootOffset : Nat}
    {env : Store32.SlotEnv} {locals : List SourceFrameHeader.Local} {entries : List Entry}
    (success : resolveEntries? layout rootOffset env locals = some entries)
    {entry : Entry} (member : entry ∈ entries) :
    entry.declaration ∈ locals ∧
      Store32.resolve? layout rootOffset env (inputOf entry.declaration) = some entry.store := by
  induction locals generalizing entries with
  | nil => simp [resolveEntries?] at success; cases success; simp at member
  | cons declaration rest ih =>
      cases storeExact : Store32.resolve? layout rootOffset env (inputOf declaration) with
      | none => simp [resolveEntries?, storeExact] at success
      | some store =>
          cases tailExact : resolveEntries? layout rootOffset env rest with
          | none => simp [resolveEntries?, storeExact, tailExact] at success
          | some tail =>
              simp [resolveEntries?, storeExact, tailExact] at success
              cases success
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact ⟨List.mem_cons_self, storeExact⟩
              · obtain ⟨sourceMember, exact⟩ := ih tailExact member
                exact ⟨List.mem_cons_of_mem _ sourceMember, exact⟩

theorem Result.entry_exact (result : Result) {entry : Entry}
    (member : entry ∈ result.entries) :
    entry.declaration ∈ result.frame.header.locals ∧
      Store32.resolve? result.frame.layout result.rootOffset
        (SourceStore.slotEnv result.frame.slots) (inputOf entry.declaration) = some entry.store :=
  resolveEntries?_member result.entriesExact member

theorem Result.entry_width (result : Result) {entry : Entry}
    (member : entry ∈ result.entries) : entry.store.range.size = 4 := by
  obtain ⟨_, exact⟩ := result.entry_exact member
  rw [Store32.range_eq_rspRootOffset_add_displacement]

theorem Result.entry_range_in_frame (result : Result) {entry : Entry}
    (member : entry ∈ result.entries) :
    (result.frame.layout.frameRange.shift result.rootOffset).Contains entry.store.range := by
  exact Store32.range_in_frame_of_resolve? (result.entry_exact member).2

theorem Result.entry_writeBytes (result : Result) {entry : Entry}
    (member : entry ∈ result.entries) :
    entry.store.writeBytes = le32 (BitVec.ofNat 32 entry.declaration.initialValue.toNat) := by
  exact Store32.writeBytes_of_resolve? (result.entry_exact member).2

theorem Result.entry_encoding_decodes (result : Result) {entry : Entry}
    (member : entry ∈ result.entries) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (entry.store.encoding.toBytes ++ rest) = .ok (entry.store.encoding, rest) :=
  Store32.encoding_decodes_of_resolve? (result.entry_exact member).2 rest

end Grass.Assembly.SourceInitialization
