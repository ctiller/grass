import Grass.Assembly.SourceInput

/-! Strict parsing of the authored wrapper around a `MachineSource` body. -/
namespace Grass.Assembly.SourceFrameHeader

open Grass.Assembly.SourceInput

structure Local where
  name : String
  initialValue : UInt32
deriving Repr, DecidableEq

structure Header where
  planName : String
  locals : List Local
  callFrameName : String
  staticsName : String
deriving Repr, DecidableEq

private inductive Token where
  | ident (value : String)
  | decimal (value : UInt32)
  | leftParen | rightParen | colon | assign
deriving Repr, DecidableEq

@[reducible] private def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

@[reducible] private def identFirst (c : Char) : Bool := asciiLetter c || c = '_'
@[reducible] private def identRest (c : Char) : Bool := identFirst c || c.isDigit
@[reducible] private def whitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

@[reducible] private def decimalValue? (digits : List Char) : Option UInt32 :=
  let step (n : Nat) (c : Char) : Option Nat :=
    let digit := c.toNat - '0'.toNat
    let candidate := n * 10 + digit
    if candidate < UInt32.size then some candidate else none
  (digits.foldlM step 0).map UInt32.ofNat

@[reducible] private def lexAux : Nat → List Char → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, c :: rest =>
    if whitespace c then lexAux fuel rest
    else if identFirst c then
      let tail := rest.takeWhile identRest
      let remaining := rest.drop tail.length
      (lexAux fuel remaining).map (.ident (String.ofList (c :: tail)) :: ·)
    else if c.isDigit then
      let tail := rest.takeWhile Char.isDigit
      let remaining := rest.drop tail.length
      match decimalValue? (c :: tail), lexAux fuel remaining with
      | some value, some tokens => some (.decimal value :: tokens)
      | _, _ => none
    else match c, rest with
      | ':', '=' :: more => (lexAux fuel more).map (.assign :: ·)
      | '(', _ => (lexAux fuel rest).map (.leftParen :: ·)
      | ')', _ => (lexAux fuel rest).map (.rightParen :: ·)
      | ':', _ => (lexAux fuel rest).map (.colon :: ·)
      | _, _ => none

@[reducible] private def lex (chars : List Char) : Option (List Token) :=
  lexAux (chars.length + 1) chars

@[reducible] private def parseLocals :
    List Token → List Local → Option (List Local × List Token)
  | .ident "withStack" :: .leftParen :: .ident name :: .colon ::
      .ident "UInt32" :: .assign :: .decimal value :: .rightParen :: rest, locals =>
    if locals.any (fun entry => entry.name = name) then none
    else parseLocals rest (locals ++ [⟨name, value⟩])
  | tokens, locals => some (locals, tokens)

@[reducible] private def parseTokens? : List Token → Option Header
  | .colon :: .ident "MachineSource" :: .ident planName :: .assign :: rest => do
      let (locals, rest) ← parseLocals rest []
      match rest with
      | [.ident "withCallFrame", .ident callFrameName, .ident "asm_source",
          .leftParen, .ident "statics", .assign, .ident staticsName, .rightParen] =>
        some ⟨planName, locals, callFrameName, staticsName⟩
      | _ => none
  | _ => none

@[reducible] def parseChars? (chars : List Char) : Option Header :=
  (lex chars).bind parseTokens?

@[reducible] def parse? (body : Body) : Option Header := parseChars? body.headerChars

end Grass.Assembly.SourceFrameHeader
