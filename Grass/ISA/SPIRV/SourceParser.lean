import Grass.ISA.SPIRV.SourceSyntax

/-! A bounded, total lexer and statement splitter for captured SPIR-V assembly
source.  This deliberately accepts syntax only: instruction names and operand
meanings remain the responsibility of the typed SPIR-V reader. -/
namespace Grass.ISA.SPIRV.SourceParser

open Grass.ISA.SPIRV.SourceSyntax

private inductive TokenKind where
  | atom (value : Atom)
  | assign
  deriving DecidableEq, Repr

private structure Token where
  kind : TokenKind
  start : Nat
  finish : Nat
  deriving DecidableEq, Repr

private def whitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- A bare source word is deliberately broad; later phases own SPIR-V typing. -/
private def bareChar (c : Char) : Bool :=
  !whitespace c && c != '%' && c != '=' && c != '"' && c != ';'

private def identifierChar (c : Char) : Bool := bareChar c

@[reducible] private def quotedTail : List Char → List Char → Nat → Option (String × List Char × Nat)
  | [], _, _ => none
  | '\\' :: _, _, _ => none
  | '"' :: rest, reversed, width => some (String.ofList reversed.reverse, rest, width + 1)
  | c :: rest, reversed, width => quotedTail rest (c :: reversed) (width + 1)

@[reducible] private def lexAux : Nat → Nat → List Char → Option (List Token)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | fuel + 1, position, c :: rest =>
    if whitespace c then
      lexAux fuel (position + 1) rest
    else if c = ';' then
      -- SPIR-V's `;` comments are not part of this bounded grammar.
      none
    else if c = '%' then
      let nameChars := rest.takeWhile identifierChar
      if nameChars.isEmpty then none
      else
        let remaining := rest.drop nameChars.length
        (lexAux fuel (position + nameChars.length + 1) remaining).map
          (⟨.atom (.id (String.ofList nameChars)), position, position + nameChars.length + 1⟩ :: ·)
    else if c = '=' then
      (lexAux fuel (position + 1) rest).map (⟨.assign, position, position + 1⟩ :: ·)
    else if c = '"' then
      match quotedTail rest [] 1 with
      | none => none
      | some (value, remaining, width) =>
        match remaining with
        | next :: _ =>
          if whitespace next then
            (lexAux fuel (position + width) remaining).map
              (⟨.atom (.quoted value), position, position + width⟩ :: ·)
          else none
        | [] =>
          (lexAux fuel (position + width) remaining).map
            (⟨.atom (.quoted value), position, position + width⟩ :: ·)
    else if bareChar c then
      let tail := rest.takeWhile bareChar
      let remaining := rest.drop tail.length
      (lexAux fuel (position + tail.length + 1) remaining).map
        (⟨.atom (.word (String.ofList (c :: tail))), position, position + tail.length + 1⟩ :: ·)
    else none

@[reducible] private def lex (chars : List Char) : Option (List Token) :=
  lexAux (chars.length + 1) 0 chars

@[reducible] private def opcode? : Atom → Option String
  | .word value =>
    match value.toList with
    | 'O' :: 'p' :: _ => some value
    | _ => none
  | _ => none

@[reducible] private def beginsStatement : List Token → Bool
  | ⟨.atom (.id _), _, _⟩ :: ⟨.assign, _, _⟩ :: _ => true
  | ⟨.atom atom, _, _⟩ :: _ => (opcode? atom).isSome
  | _ => false

@[reducible] private def collectOperands : List Token → List Atom → Nat → Option (List Atom × List Token × Nat)
  | [], operands, finish => some (operands.reverse, [], finish)
  | tokens, operands, finish =>
    if beginsStatement tokens then some (operands.reverse, tokens, finish)
    else match tokens with
      | ⟨.atom atom, _, tokenFinish⟩ :: rest =>
        collectOperands rest (atom :: operands) tokenFinish
      | _ => none

@[reducible] private def parseOne? : List Token → Option (Statement × List Token)
  | ⟨.atom (.id result), start, _⟩ :: ⟨.assign, _, _⟩ :: ⟨.atom opcode, _, opcodeFinish⟩ :: rest => do
    let opcode ← opcode? opcode
    let (operands, remaining, finish) ← collectOperands rest [] opcodeFinish
    some (⟨some result, opcode, operands, start, finish⟩, remaining)
  | ⟨.atom opcode, start, finish⟩ :: rest => do
    let opcode ← opcode? opcode
    let (operands, remaining, finish) ← collectOperands rest [] finish
    some (⟨none, opcode, operands, start, finish⟩, remaining)
  | _ => none

@[reducible] private def parseTokensAux : Nat → List Token → List Statement → Option (List Statement)
  | 0, _, _ => none
  | _ + 1, [], statements => some statements.reverse
  | fuel + 1, tokens, statements => do
    let (statement, remaining) ← parseOne? tokens
    parseTokensAux fuel remaining (statement :: statements)

@[reducible] private def parseTokens? (tokens : List Token) : Option (List Statement) :=
  parseTokensAux (tokens.length + 1) tokens []

/-- A statement span is a half-open range within the captured body. -/
def Statement.Framed (body : List Char) (statement : Statement) : Bool :=
  statement.start ≤ statement.finish && statement.finish ≤ body.length

/-- Parse the complete captured SPIR-V assembly body, refusing every unconsumed
or unsupported character.  Backslash escapes and `;` comments are intentionally
rejected until their source spelling has a corresponding semantic representation. -/
@[reducible] def parseBody? (body : List Char) : Option (List Statement) :=
  match lex body with
  | none => none
  | some tokens =>
    match parseTokens? tokens with
    | none => none
    | some statements =>
      if statements.all (Statement.Framed body) then some statements else none

theorem parseBody?_framed {body : List Char} {statements : List Statement}
    (parsed : parseBody? body = some statements) :
    ∀ statement ∈ statements, Statement.Framed body statement = true := by
  unfold parseBody? at parsed
  split at parsed
  · simp_all
  · split at parsed
    · simp_all
    · split at parsed <;> simp_all

end Grass.ISA.SPIRV.SourceParser
