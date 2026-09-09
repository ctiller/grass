import Grass.Assembly.SourceInput
import Grass.ISA.X86.BasicInstructions

/-! Complete syntactic ingress for the instruction forms used by Spike 1. -/
namespace Grass.Assembly.X86Source

structure Register where
  gpr : Grass.ISA.X86.Gpr
  width : Grass.ISA.X86.BasicInstructions.Width
deriving Repr, DecidableEq
inductive Operand where
  | register (value : Register) | immediate (value : Nat) | symbol (name : String)
  | address (name : String) | sizeOf (name : String) | ripMemory (name : String)
  | qualified (owner field : String)
deriving Repr, DecidableEq
inductive Mnemonic where
  | push | mov | test | cmp | lea | call | jz | je | ja | jmp | add | sub | xor | ud2 | arg
deriving Repr, DecidableEq
structure Instruction where
  mnemonic : Mnemonic
  operands : List Operand
deriving Repr, DecidableEq
inductive AnnotationKind where
  | placement | invariant | terminal | audit | violationEdge | containmentTail
deriving Repr, DecidableEq
structure Annotation where
  kind : AnnotationKind
  arguments : List String
deriving Repr, DecidableEq
inductive Statement where
  | label (name : String) (annotations : List Annotation)
  | instruction (value : Instruction) (annotations : List Annotation)
deriving Repr, DecidableEq
structure LocatedStatement where
  lineNumber : Nat
  text : String
  statement : Statement
deriving Repr, DecidableEq
inductive Error where | unsupported (line : Nat) (text : String) | malformed (line : Nat) (text : String)
deriving Repr, DecidableEq

private inductive Lexeme where
  | word (chars : List Char) | comma | colon | at | lp | rp | lb | rb | plus | dot | assign
deriving Repr, DecidableEq
@[reducible] private def punct (c : Char) : Bool := c ∈ [',',':','@','(',')','[',']','+','.']
@[reducible] private def lexLine : List Char → List Char → List Lexeme
  | [], word => if word.isEmpty then [] else [.word word.reverse]
  | c::cs, word =>
    let tail := fun () => lexLine cs []
    let flushed := fun xs => if word.isEmpty then xs else .word word.reverse :: xs
    if c = ' ' || c = '\t' || c = '\r' then flushed (tail ())
    else if c = ':' && cs.head? = some '=' then
      flushed (.assign :: lexLine (cs.drop 1) [])
    else if punct c then
      let mark := match c with
        | ',' => .comma | ':' => .colon | '@' => .at | '(' => .lp | ')' => .rp
        | '[' => .lb | ']' => .rb | '+' => .plus | _ => .dot
      flushed (mark :: tail ())
    else lexLine cs (c::word)
termination_by chars _ => chars.length
decreasing_by all_goals simp_wf <;> omega

@[reducible] private def word? : Lexeme → Option String
  | .word cs => some (String.ofList cs) | _ => none
@[reducible] private def reg? (s : String) : Option Register :=
  let found : Option (Grass.ISA.X86.Gpr × Grass.ISA.X86.BasicInstructions.Width) := match s with
    | "eax" => some (.rax,.w32) | "ecx" => some (.rcx,.w32) | "edx" => some (.rdx,.w32)
    | "ebx" => some (.rbx,.w32) | "esp" => some (.rsp,.w32) | "ebp" => some (.rbp,.w32)
    | "esi" => some (.rsi,.w32) | "edi" => some (.rdi,.w32) | "r8d" => some (.r8,.w32)
    | "r9d" => some (.r9,.w32) | "r10d" => some (.r10,.w32) | "r11d" => some (.r11,.w32)
    | "r12d" => some (.r12,.w32) | "r13d" => some (.r13,.w32)
    | "r14d" => some (.r14,.w32) | "r15d" => some (.r15,.w32)
    | "rax" => some (.rax,.w64) | "rcx" => some (.rcx,.w64) | "rdx" => some (.rdx,.w64)
    | "rbx" => some (.rbx,.w64) | "rsp" => some (.rsp,.w64) | "rbp" => some (.rbp,.w64)
    | "rsi" => some (.rsi,.w64) | "rdi" => some (.rdi,.w64) | "r8" => some (.r8,.w64)
    | "r9" => some (.r9,.w64) | "r10" => some (.r10,.w64) | "r11" => some (.r11,.w64)
    | "r12" => some (.r12,.w64) | "r13" => some (.r13,.w64)
    | "r14" => some (.r14,.w64) | "r15" => some (.r15,.w64) | _ => none
  found.map fun pair => ⟨pair.1,pair.2⟩
@[reducible] private def natChars? (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else cs.foldlM (fun n c =>
    if c.isDigit then some (n*10 + (c.toNat-'0'.toNat)) else none) 0
@[reducible] private def operand? : List Lexeme → Option Operand
  | [.word a] =>
    let s := String.ofList a
    match reg? s with
    | some r => some (.register r)
    | none =>
      match natChars? a with
      | some n => some (.immediate n)
      | none => some (.symbol s)
  | [.word a,.dot,.word addr] =>
    if addr = "addr".toList then some (.address (String.ofList a))
    else some (.qualified (String.ofList a) (String.ofList addr))
  | [.word size,.lp,.word a,.rp] =>
    if size = "sizeof".toList then some (.sizeOf (String.ofList a)) else none
  | [.lb,.word rip,.plus,.word a,.rb] =>
    if rip = "rip".toList then some (.ripMemory (String.ofList a)) else none
  | [.word q,.word ptr,.lb,.word rip,.plus,.word a,.rb] =>
    if q="qword".toList && ptr="ptr".toList && rip="rip".toList then
      some (.ripMemory (String.ofList a)) else none
  | _ => none

@[reducible] private def splitAt (separator : Lexeme) : List Lexeme → List Lexeme → List (List Lexeme)
  | [], current => [current.reverse]
  | x::xs, current => if x = separator then current.reverse :: splitAt separator xs []
    else splitAt separator xs (x::current)
@[reducible] private def splitComma (xs : List Lexeme) : List (List Lexeme) :=
  if xs.isEmpty then [] else splitAt .comma xs []
@[reducible] private def operands? (xs : List Lexeme) : Option (List Operand) := (splitComma xs).mapM operand?
@[reducible] private def mnemonic? (s : String) : Option Mnemonic := match s with
  | "push" => some .push | "mov" => some .mov | "test" => some .test | "cmp" => some .cmp
  | "lea" => some .lea | "call" => some .call | "jz" => some .jz | "je" => some .je
  | "ja" => some .ja | "jmp" => some .jmp | "add" => some .add | "sub" => some .sub
  | "xor" => some .xor | "ud2" => some .ud2 | "arg" => some .arg | _ => none
@[reducible] private def arity : Mnemonic → Nat
  | .push | .call | .jz | .je | .ja | .jmp => 1 | .ud2 => 0 | _ => 2
@[reducible] def WellShaped : Mnemonic → List Operand → Bool
  | .push, [.register ⟨_,.w64⟩] => true
  | .call, [.ripMemory _] => true
  | .jz, [.symbol _] => true | .je, [.symbol _] => true
  | .ja, [.symbol _] => true | .jmp, [.symbol _] => true
  | .lea, [.register ⟨_,.w64⟩, .ripMemory _] => true
  | .lea, [.register ⟨_,.w64⟩, .address _] => true
  | .test, [.register ⟨_, left⟩, .register ⟨_, right⟩] => decide (left = right)
  | .test, [.register _, .immediate _] => true
  | .cmp, [.register ⟨_, left⟩, .register ⟨_, right⟩] => decide (left = right)
  | .cmp, [.register _, .immediate _] => true
  | .cmp, [.register _, .symbol _] => true
  | .add, [.register ⟨_, left⟩, .register ⟨_, right⟩] => decide (left = right)
  | .sub, [.register ⟨_, left⟩, .register ⟨_, right⟩] => decide (left = right)
  | .xor, [.register ⟨_, left⟩, .register ⟨_, right⟩] => decide (left = right)
  | .mov, [.register ⟨_, left⟩, .register ⟨_, right⟩] => decide (left = right)
  | .mov, [.register _, .immediate _] => true
  | .mov, [.register _, .symbol _] => true | .mov, [.register _, .sizeOf _] => true
  | .mov, [.symbol _, .immediate _] => true
  | .arg, [.qualified _ _, .immediate _] => true
  | .ud2, [] => true
  | _, _ => false
@[reducible] private def instruction? : List Lexeme → Option Instruction
  | .word m :: rest => do
    let some mnemonic := mnemonic? (String.ofList m) | none
    let some operands := operands? rest | none
    if operands.length = arity mnemonic && WellShaped mnemonic operands then
      some { mnemonic, operands } else none
  | _ => none

@[reducible] private def annotationKind? (s : String) : Option AnnotationKind := match s with
  | "placement" => some .placement | "invariant" => some .invariant
  | "terminal" => some .terminal | "audit" => some .audit
  | "violation_edge" => some .violationEdge | "containment_tail" => some .containmentTail
  | _ => none

@[reducible] private def commaWords? : List Lexeme → Option (List String)
  | [] => some []
  | [.word chars] => some [String.ofList chars]
  | .word chars :: .comma :: rest => do
      if rest.isEmpty then none else do
        let tail ← commaWords? rest
        some (String.ofList chars :: tail)
  | _ => none

@[reducible] private def placementArguments? : List Lexeme → Option (List String)
  | [] => some []
  | [.word key, .assign, .word value] =>
      some [String.ofList key, String.ofList value]
  | .word key :: .assign :: .word value :: .comma :: rest => do
      if rest.isEmpty then none else do
        let tail ← placementArguments? rest
        some (String.ofList key :: String.ofList value :: tail)
  | _ => none

@[reducible] private def evenKeys : List String → List String
  | [] => []
  | key :: _ :: rest => key :: evenKeys rest
  | _ => []

@[reducible] private def annotation? : List Lexeme → Option Annotation
  | .word name :: rest => do
    let some kind := annotationKind? (String.ofList name) | none
    let arguments ← match kind with
      | .terminal | .audit | .violationEdge | .containmentTail =>
          match rest with
          | [.lp, .dot, .word tag, .rp] => some [String.ofList tag]
          | _ => none
      | .invariant =>
          match rest with
          | .word invariant :: .lp :: inside =>
              match inside.reverse with
              | .rp :: reversedArgs => do
                  let args ← commaWords? reversedArgs.reverse
                  some (String.ofList invariant :: args)
              | _ => none
          | _ => none
      | .placement =>
          match rest with
          | .lb :: inside =>
              match inside.reverse with
              | .rb :: reversedAssignments => do
                  let args ← placementArguments? reversedAssignments.reverse
                  if (evenKeys args).Nodup then some args else none
              | _ => none
          | _ => none
    some { kind, arguments }
  | _ => none
@[reducible] private def splitAnnotations : List Lexeme → List Lexeme × List (List Lexeme)
  | xs =>
    let main := xs.takeWhile (· != .at)
    let rest := xs.drop main.length
    (main, match rest with | [] => [] | .at::more => splitAt .at more [] | _ => [])

@[reducible] private def parseStatement? (chars : List Char) : Option Statement :=
  let (main, rawAnnotations) := splitAnnotations (lexLine chars [])
  do
    let annotations ← rawAnnotations.mapM annotation?
    match main with
    | [.word name,.colon] => some (.label (String.ofList name) annotations)
    | _ => some (.instruction (← instruction? main) annotations)

@[reducible] private def annotationLine? (chars : List Char) : Option (List Annotation) :=
  let (main, raw) := splitAnnotations (lexLine chars [])
  if main.isEmpty then raw.mapM annotation? else none

@[reducible] private def appendAnnotations (statement : Statement) (more : List Annotation) : Statement :=
  match statement with
  | .label name annotations => .label name (annotations ++ more)
  | .instruction value annotations => .instruction value (annotations ++ more)

@[reducible] private def blank (chars : List Char) : Bool := chars.all fun c => c=' ' || c='\t' || c='\r'
@[reducible] private def splitLines : List Char → List (List Char)
  | [] => [[]] | '\n'::rest => []::splitLines rest | c::rest =>
    match splitLines rest with | line::lines => (c::line)::lines | [] => [[c]]

@[reducible] private def parseLines : List (List Char) → Nat → List LocatedStatement →
    Except Error (List LocatedStatement)
  | [], _, acc => .ok acc.reverse
  | line::rest, number, acc =>
    if blank line then parseLines rest (number+1) acc else
    match annotationLine? line with
    | some more => match acc with
      | [] => .error (.malformed number (String.ofList line))
      | previous::prior =>
        let updated := { previous with
          text := previous.text ++ "\n" ++ String.ofList line
          statement := appendAnnotations previous.statement more }
        parseLines rest (number+1) (updated::prior)
    | none => match parseStatement? line with
      | none => .error (.unsupported number (String.ofList line))
      | some statement =>
        parseLines rest (number+1)
          ({ lineNumber := number, text := String.ofList line, statement }::acc)

@[reducible] def parseBody (body : SourceInput.Body) : Except Error (List LocatedStatement) :=
  parseLines (splitLines body.bodyChars) 1 []

end Grass.Assembly.X86Source

