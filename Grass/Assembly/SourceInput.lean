/-! Narrow, lossless ingress for the actual Spike 1 `asm_source` body. -/
namespace Grass.Assembly.SourceInput

inductive ParsedLine where
  | blank | label (name : String)
  | symbolicStore (destination : String) (value : Nat)
  | unsupported
deriving Repr, DecidableEq
structure SourceLine where
  number : Nat
  text : String
  parsed : ParsedLine
deriving Repr, DecidableEq
structure Body where
  headerText : String
  headerChars : List Char
  text : String
  lines : List SourceLine
deriving Repr, DecidableEq
inductive Error where | missing | ambiguous (count : Nat) | malformed
deriving Repr, DecidableEq
inductive TokenKind where
  | word (value : String) | leftParen | rightParen | colon | assign | leftBrace | rightBrace
deriving Repr, DecidableEq
structure Token where
  kind : TokenKind
  start : Nat
  finish : Nat
deriving Repr, DecidableEq

private def wordChar (c : Char) : Bool := c.isAlphanum || c = '_' || c = '«' || c = '»'
@[reducible] private def lexAux :
    Nat → List Char → Nat → Bool → Nat → Bool → List Char → List Token → Option (List Token)
  | 0, _, _, _, _, _, _, _ => none
  | _ + 1, [], pos, _, depth, quoted, wordRev, acc =>
    if depth != 0 || quoted then none
    else
      let acc := if wordRev.isEmpty then acc else
        ⟨.word (String.ofList wordRev.reverse), pos-wordRev.length, pos⟩ :: acc
      some acc.reverse
  | fuel + 1, c::rest, pos, lineComment, depth, quoted, wordRev, acc =>
    let flush := if wordRev.isEmpty then acc else
      ⟨.word (String.ofList wordRev.reverse), pos-wordRev.length, pos⟩ :: acc
    if lineComment then lexAux fuel rest (Nat.succ pos) (c != '\n') depth quoted wordRev acc
    else if depth != 0 then match c, rest with
      | '/', '-'::more => lexAux fuel more (Nat.succ (Nat.succ pos)) false (depth+1) quoted wordRev acc
      | '-', '/'::more => lexAux fuel more (Nat.succ (Nat.succ pos)) false (depth-1) quoted wordRev acc
      | _, _ => lexAux fuel rest (Nat.succ pos) false depth quoted wordRev acc
    else if quoted then
      if c='\\' then match rest with
        | [] => none
        | _::more => lexAux fuel more (Nat.succ (Nat.succ pos)) false 0 true wordRev acc
      else lexAux fuel rest (Nat.succ pos) false 0 (c != '"') wordRev acc
    else
      let emit (kind : TokenKind) (n : Nat) (more : List Char) :=
        lexAux fuel more (pos + n) false 0 false [] (⟨kind,pos,pos + n⟩::flush)
      match c, rest with
      | '-', '-'::more => lexAux fuel more (Nat.succ (Nat.succ pos)) true 0 false [] flush
      | '/', '-'::more => lexAux fuel more (Nat.succ (Nat.succ pos)) false 1 false [] flush
      | ':', '='::more => emit .assign 2 more
      | '"', _ => lexAux fuel rest (Nat.succ pos) false 0 true [] flush
      | '(', _ => emit .leftParen 1 rest
      | ')', _ => emit .rightParen 1 rest
      | ':', _ => emit .colon 1 rest
      | '{', _ => emit .leftBrace 1 rest
      | '}', _ => emit .rightBrace 1 rest
      | _, _ => if wordChar c then lexAux fuel rest (Nat.succ pos) false 0 false (c::wordRev) acc
        else lexAux fuel rest (Nat.succ pos) false 0 false [] flush
@[reducible] def tokens (source : String) : Option (List Token) :=
  if source.toList.contains '\'' then none
  else lexAux (source.toList.length + 1) source.toList 0 false 0 false [] []

@[reducible] def tokensChars (source : List Char) : Option (List Token) :=
  if source.contains '\'' then none
  else lexAux (source.length + 1) source 0 false 0 false [] []
@[reducible] private def bodyEnd? : List Token → Nat → Option Nat
  | [], _ => none
  | t::ts, depth => match t.kind with
    | .leftBrace => bodyEnd? ts (depth+1)
    | .rightBrace => if depth=1 then some t.start else bodyEnd? ts (depth-1)
    | _ => bodyEnd? ts depth
@[reducible] private def assemblyStart? : List Token → Option (Token × List Token)
  | [] => none
  | t::ts => match t.kind with
    | .word "def" => none
    | .word "asm_source" =>
      let rec brace : List Token → Option (Token × List Token)
        | [] => none
        | b :: after => match b.kind with
          | .leftBrace => some (b, after)
          | .word "asm_source" | .word "def" | .rightBrace => none
          | _ => brace after
      brace ts
    | _ => assemblyStart? ts
@[reducible] private def candidates : List Token → List (Nat × Nat × Nat)
  | a::b::ts => match a.kind, b.kind with
    | .word "def", .word "helloSource" => match assemblyStart? ts with
      | some (brace, after) => match bodyEnd? after 1 with
        | some finish => (b.finish, brace.start, finish)::candidates ts | none => candidates ts
      | none => candidates ts
    | _, _ => candidates (b::ts)
  | _ => []

@[reducible] private def helloSourceCount : List Token → Nat
  | a :: b :: rest =>
    (if a.kind = .word "def" && b.kind = .word "helloSource" then 1 else 0) +
      helloSourceCount (b :: rest)
  | _ => 0

@[reducible] private def space (c : Char) : Bool := c = ' ' || c = '\t' || c = '\r'
@[reducible] private def trimLeft (cs : List Char) : List Char := cs.dropWhile space
@[reducible] private def trimRight (cs : List Char) : List Char := (cs.reverse.dropWhile space).reverse
@[reducible] private def decimal? (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else cs.foldlM (fun n c =>
    if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none) 0
@[reducible] private def parseLineChars (line : List Char) : ParsedLine :=
  let cs := trimRight (trimLeft line)
  if cs.isEmpty then .blank
  else if cs.getLast? = some ':' then
    let name := cs.dropLast
    if name.any space then .unsupported else .label (String.ofList name)
  else if cs.take 4 = ['m','o','v',' '] then
    let operand := cs.drop 4
    let destination := operand.takeWhile (· != ',')
    match operand.drop destination.length with
    | ',' :: valueChars => match decimal? (trimLeft valueChars) with
      | some value => .symbolicStore (String.ofList (trimRight destination)) value
      | none => .unsupported
    | _ => .unsupported
  else .unsupported
@[reducible] private def containsPair (first second : Char) : List Char → Bool
  | a :: b :: rest => (a = first && b = second) || containsPair first second (b :: rest)
  | _ => false

@[reducible] private def splitLines : List Char → List (List Char)
  | [] => [[]]
  | '\n' :: rest => [] :: splitLines rest
  | c :: rest =>
      match splitLines rest with
      | [] => [[c]]
      | line :: lines => (c :: line) :: lines

@[reducible] private def sourceLines (chars : List Char) : List SourceLine :=
  let unsafeLexicalContext := containsPair '/' '-' chars ||
    chars.contains '"' || containsPair '-' '-' chars
  let rec number (parse : List Char → ParsedLine) : List (List Char) → Nat → List SourceLine
    | [], _ => []
    | line :: rest, index =>
      ⟨index, String.ofList line, parse line⟩ :: number parse rest (index + 1)
  let lines := splitLines chars
  if unsafeLexicalContext then number (fun _ => .unsupported) lines 1
  else number parseLineChars lines 1

@[reducible] def extractHelloSourceChars (source : List Char) : Except Error Body :=
  match tokensChars source with
  | none => .error .malformed
  | some ts =>
    let found := candidates ts
    if found.length != helloSourceCount ts then .error .malformed else match found with
    | [] => .error .missing
    | [(hs, bs, finish)] =>
      let header := String.ofList ((source.drop hs).take (bs-hs))
      let bodyChars := (source.drop (bs+1)).take (finish-bs-1)
      let text := String.ofList bodyChars
      .ok ⟨header, (source.drop hs).take (bs-hs), text, sourceLines bodyChars⟩
    | many => .error (.ambiguous many.length)

@[reducible] def extractHelloSource (source : String) : Except Error Body :=
  extractHelloSourceChars source.toList

@[reducible] def symbolicStores (body : Body) : List (String × Nat) := body.lines.filterMap fun line =>
  match line.parsed with | .symbolicStore dst value => some (dst,value) | _ => none

/-- All stack declarations, provided every declaration uses the supported UInt32 form. -/
@[reducible] def uint32StackSlots (body : Body) : Option (List String) := match tokensChars body.headerChars with
  | none => none
  | some ts =>
    let rec scan : List Token → Option (List String)
      | ⟨.word "withStack",_,_⟩ :: ⟨.leftParen,_,_⟩ :: ⟨.word name,_,_⟩ ::
          ⟨.colon,_,_⟩ :: ⟨.word "UInt32",_,_⟩ :: ⟨.assign,_,_⟩ ::
          ⟨.word _,_,_⟩ :: ⟨.rightParen,_,_⟩ :: rest => (scan rest).map (name :: ·)
      | ⟨.word "withStack",_,_⟩ :: _ => none
      | _::rest => scan rest
      | [] => some []
    scan ts

end Grass.Assembly.SourceInput



