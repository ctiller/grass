/-!
# A WGSL module: a small typed AST and its text encoding

This module gives `Grass.Target.ShaderLanguage.Module` a concrete shape for
WGSL: struct declarations with `@location`/`@builtin` fields, `var<uniform>`
bindings with `@group`/`@binding`, `fn` declarations with an optional
`@vertex`/`@fragment` stage attribute, and a small statement/expression
language (`let`/`var`/`return`/assignment; identifiers, member access,
builtin calls, and one binary operator application). It proves the
encode/decode round trip the seam requires; it is not a WGSL validator, type
checker, or uniformity analysis, and it does not implement WGSL's full
grammar.

The source rule follows the W3C WGSL Candidate Recommendation Draft, 31
August 2026: https://www.w3.org/TR/2026/CRD-WGSL-20260831/

## Deliberate departures from ordinary WGSL text, and why

`decode (encode m) = some m` must hold for every `m : Module` with no side
condition, so (as in `Grass.Shader.SPIRV.Module`, which explains the same
tension for SPIR-V) every choice below is shaped to make that an
unconditional theorem rather than a claim about well-behaved input:

* **Every token is rendered space-separated**, including punctuation
  (`( x )` rather than `(x)`). WGSL's grammar allows arbitrary whitespace
  between tokens, so this is still acceptable WGSL text; it turns lexing
  into "split on the single ASCII space `Token.render` never itself
  contains", which is proved once and reused everywhere, rather than a
  maximal-munch lexer over arbitrary adjacent characters.
* **Identifiers are `$`-prefixed and numeric literals are `#`/`~`-prefixed**
  (`#` for non-negative, `~` for negative) in the token spelling. WGSL
  identifiers cannot itself contain `$`, `#`, or `~`, so this is a
  conservative subset of legal WGSL identifiers, not an extension of the
  syntax; it exists so the lexer never has to decide "is this spelling one
  of the fixed keywords, or a name that happens to collide with one" — the
  leading sigil decides it unconditionally, for every `String` the type
  admits, with no wellformedness side condition on identifier spelling.
* **A numeral's optional fractional part is encoded inside its own token's
  characters** (`#0.25`, one token) rather than as a separate `.` token
  followed by another numeral token. A per-token internal `.` is safe to
  locate because a token's characters are already space-delimited before
  anything looks at them; a `.` used as a separate token between two numeral
  tokens would not be, since nothing would stop it from splicing onto an
  unrelated numeral that happened to follow.
* **Every variable-length list (struct fields, function parameters, a
  function body's statements, a call's arguments) is terminated by a
  dedicated end token** rather than delimited by matching an opening and a
  closing bracket. Bracket matching needs a well-founded recursion on
  nesting depth to parse back; an explicit terminator needs only the same
  fuel-bounded repetition already proved once in
  `Grass.Shader.SPIRV.Module.decodeInstrsFuel` (mirrored here as
  `parseListFuel`) and reused at every list site. The rendered text still
  carries real `{`/`}`/`(`/`)` delimiters for readability; the terminator is
  what decoding actually relies on.
* **A numeral's value is represented by its own decimal digit spelling**
  (sign, a nonempty digit run, an optional nonempty fractional digit run),
  not by a `Nat`/`Int`/`Float`. The round trip is then exact digit-for-digit
  reconstruction, with no dependency on how (or whether) Lean's `Float`
  formats a value back to the decimal string that produced it. This is a
  real cut: the module cannot express "the numeral with value one-half
  however it is spelled", only "the numeral spelled `0.5`". A construction
  that needs numeric value equality (constant folding, a real GPU numeric
  comparison) is out of scope here and would need a proved
  digit-string/`Float` correspondence lemma layered on top.

* **No expression form may be a prefix of another**, since each `ofTokens`
  inverts its `toTokens` for an *arbitrary* trailing token list rather than
  only for the suffixes the grammar happens to produce. Member access is
  therefore `.`-prefixed (`. $base $field`), a call is parenthesised around
  its callee (`( $f $a $b end )`), and a binary application is written
  prefix (`+ $a $b`), so the first token alone decides the form. Written
  infix, `$x` would be a prefix of `$x . $f`, and `$f` a prefix of
  `$f ( … )`, and the round trip would hold only for suffixes some other
  argument had to supply. See the section docstring on atoms below.

None of this is program-specific: it is vocabulary a `@vertex`/`@fragment`
pair can be built from, not the spinning cube's own shader text.
-/

namespace Grass.Shader.WGSL.Module

/-! ## Digits

A nonempty decimal digit sequence (leading digit, then more digits), used
both for numeral spellings and for `@location`/`@group`/`@binding` indices. -/

def digitChar : Fin 10 → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'

def charDigit? : Char → Option (Fin 10)
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

theorem charDigit?_digitChar (d : Fin 10) : charDigit? (digitChar d) = some d := by
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl

def digitsToChars : List (Fin 10) → List Char := List.map digitChar

def charsToDigits? : List Char → Option (List (Fin 10))
  | [] => some []
  | c :: rest => do
      let d ← charDigit? c
      let ds ← charsToDigits? rest
      some (d :: ds)

theorem charsToDigits?_digitsToChars (ds : List (Fin 10)) :
    charsToDigits? (digitsToChars ds) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      show charsToDigits? (digitChar d :: digitsToChars ds) = some (d :: ds)
      show (do let d' ← charDigit? (digitChar d); let ds' ← charsToDigits? (digitsToChars ds); some (d' :: ds')) =
        some (d :: ds)
      rw [charDigit?_digitChar]
      show (do let ds' ← charsToDigits? (digitsToChars ds); some (d :: ds')) = some (d :: ds)
      rw [ih]; rfl

/-- A nonempty decimal digit sequence: a leading digit, then zero or more. -/
structure Digits where
  negative : Bool
  digit : Fin 10
  rest : List (Fin 10)
deriving DecidableEq, Repr

def Digits.chars (d : Digits) : List Char := digitChar d.digit :: digitsToChars d.rest

/-- A numeral: an integer digit run, and an optional fractional digit run
(the digits after a `.`, always unsigned). -/
structure Numeral where
  intDigits : Digits
  fracDigits : Option (Fin 10 × List (Fin 10))
deriving DecidableEq, Repr

def Numeral.chars (n : Numeral) : List Char :=
  n.intDigits.chars ++ match n.fracDigits with
    | none => []
    | some (d, ds) => '.' :: digitChar d :: digitsToChars ds

/-- Split a character run at the first `.`, if any. Used only within one
already-space-delimited token's own characters, so there is no ambiguity
with tokens that follow — unlike a per-token sigil, a `.` chosen this way
never has to disambiguate against neighbouring tokens. -/
def splitAtDot : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: rest =>
      if c = '.' then ([], some rest)
      else
        let (pre, post) := splitAtDot rest
        (c :: pre, post)

theorem splitAtDot_nil (cs : List Char) (h : '.' ∉ cs) : splitAtDot cs = (cs, none) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc : ¬ c = '.' := fun heq => h (heq ▸ List.mem_cons_self ..)
      have hcs : '.' ∉ cs := fun hm => h (List.mem_cons_of_mem c hm)
      show splitAtDot (c :: cs) = (c :: cs, none)
      simp only [splitAtDot, if_neg hc, ih hcs]

theorem splitAtDot_dot (cs rest : List Char) (h : '.' ∉ cs) :
    splitAtDot (cs ++ '.' :: rest) = (cs, some rest) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc : ¬ c = '.' := fun heq => h (heq ▸ List.mem_cons_self ..)
      have hcs : '.' ∉ cs := fun hm => h (List.mem_cons_of_mem c hm)
      show splitAtDot (c :: (cs ++ '.' :: rest)) = (c :: cs, some rest)
      simp only [splitAtDot, if_neg hc, ih hcs]

theorem digitChar_ne_dot (d : Fin 10) : digitChar d ≠ '.' := by
  match d with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide

theorem digitsToChars_noDot (ds : List (Fin 10)) : '.' ∉ digitsToChars ds := by
  induction ds with
  | nil => simp [digitsToChars]
  | cons d ds ih =>
      simp only [digitsToChars, List.map_cons, List.mem_cons]
      exact fun h => h.elim (fun heq => digitChar_ne_dot d heq.symm) ih

theorem Digits.noDot (d : Digits) : '.' ∉ d.chars := by
  simp only [Digits.chars, List.mem_cons]
  exact fun h => h.elim (fun heq => digitChar_ne_dot d.digit heq.symm) (digitsToChars_noDot d.rest)

/-- Parse a numeral's characters (already sign-stripped, from within one
token's own span). -/
def parseNumeralChars? (negative : Bool) (cs : List Char) : Option Numeral :=
  match splitAtDot cs with
  | (intChars, fracChars?) =>
      match intChars with
      | [] => none
      | d0 :: ds0 =>
          match charDigit? d0, charsToDigits? ds0 with
          | some d0', some ds0' =>
              match fracChars? with
              | none => some ⟨⟨negative, d0', ds0'⟩, none⟩
              | some [] => none
              | some (fd0 :: fds0) =>
                  match charDigit? fd0, charsToDigits? fds0 with
                  | some fd0', some fds0' => some ⟨⟨negative, d0', ds0'⟩, some (fd0', fds0')⟩
                  | _, _ => none
          | _, _ => none

theorem parseNumeralChars?_chars (n : Numeral) :
    parseNumeralChars? n.intDigits.negative n.chars = some n := by
  obtain ⟨⟨negative, digit, rest⟩, fracDigits⟩ := n
  have hnodot : '.' ∉ digitChar digit :: digitsToChars rest := by
    simp only [List.mem_cons]
    exact fun h => h.elim (fun heq => digitChar_ne_dot digit heq.symm) (digitsToChars_noDot rest)
  cases fracDigits with
  | none =>
      show parseNumeralChars? negative (Digits.chars ⟨negative, digit, rest⟩ ++ []) =
        some ⟨⟨negative, digit, rest⟩, none⟩
      rw [List.append_nil]
      show parseNumeralChars? negative (digitChar digit :: digitsToChars rest) =
        some ⟨⟨negative, digit, rest⟩, none⟩
      unfold parseNumeralChars?
      rw [splitAtDot_nil (digitChar digit :: digitsToChars rest) hnodot]
      simp only [charDigit?_digitChar, charsToDigits?_digitsToChars]
  | some p =>
      obtain ⟨fdigit, frest⟩ := p
      show parseNumeralChars? negative
        (Digits.chars ⟨negative, digit, rest⟩ ++ ('.' :: digitChar fdigit :: digitsToChars frest)) =
        some ⟨⟨negative, digit, rest⟩, some (fdigit, frest)⟩
      show parseNumeralChars? negative
        ((digitChar digit :: digitsToChars rest) ++ ('.' :: (digitChar fdigit :: digitsToChars frest))) =
        some ⟨⟨negative, digit, rest⟩, some (fdigit, frest)⟩
      unfold parseNumeralChars?
      rw [splitAtDot_dot (digitChar digit :: digitsToChars rest) (digitChar fdigit :: digitsToChars frest) hnodot]
      simp only [charDigit?_digitChar, charsToDigits?_digitsToChars]

/-! ## Tokens

Every token renders to a nonempty, space-free character run; `Token.ofChars?`
inverts `Token.render` exactly (`ofChars?_render` below), for every token,
unconditionally. -/

/-- A nonempty character run excluding the four reserved sigils (space and
the identifier/numeral leading markers), so it can never be mistaken for a
keyword boundary or another token's sigil. -/
def identOk (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all (fun c => !(c == ' ' || c == '$' || c == '#' || c == '~'))

/-- An identifier-safe name: what `Atom.ident`, struct/field/parameter names,
and every other user-chosen WGSL name in this vocabulary are drawn from. -/
abbrev Name := { cs : List Char // identOk cs = true }

theorem Name.noSpace (n : Name) : ' ' ∉ n.val := by
  obtain ⟨cs, h⟩ := n
  simp only [identOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  intro hmem
  have hc := h.2 ' ' hmem
  simp at hc

theorem Name.ne_nil (n : Name) : n.val ≠ [] := by
  obtain ⟨cs, h⟩ := n
  simp only [identOk, Bool.and_eq_true] at h
  simpa using h.1

inductive Token where
  | kwStruct | kwFn | kwVar | kwLet | kwReturn | kwUniform
  | tyF32 | tyI32 | tyU32 | tyVec2 | tyVec3 | tyVec4 | tyMat4x4
  | kwVertex | kwFragment | kwCompute
  | kwLocation | kwBuiltin | kwGroup | kwBinding
  | kwEnd
  | lbrace | rbrace | lparen | rparen | langle | rangle
  | comma | semicolon | colon | equals | dot | arrow | at
  | plus | minus | star | slash
  | ident (name : Name)
  | numLit (n : Numeral)
deriving DecidableEq, Repr

def Token.render : Token → List Char
  | .kwStruct => "struct".toList | .kwFn => "fn".toList | .kwVar => "var".toList
  | .kwLet => "let".toList | .kwReturn => "return".toList | .kwUniform => "uniform".toList
  | .tyF32 => "f32".toList | .tyI32 => "i32".toList | .tyU32 => "u32".toList
  | .tyVec2 => "vec2".toList | .tyVec3 => "vec3".toList | .tyVec4 => "vec4".toList
  | .tyMat4x4 => "mat4x4".toList
  | .kwVertex => "vertex".toList | .kwFragment => "fragment".toList | .kwCompute => "compute".toList
  | .kwLocation => "location".toList | .kwBuiltin => "builtin".toList
  | .kwGroup => "group".toList | .kwBinding => "binding".toList
  | .kwEnd => "end".toList
  | .lbrace => ['{'] | .rbrace => ['}'] | .lparen => ['('] | .rparen => [')']
  | .langle => ['<'] | .rangle => ['>']
  | .comma => [','] | .semicolon => [';'] | .colon => [':'] | .equals => ['=']
  | .dot => ['.'] | .arrow => "->".toList | .at => ['@']
  | .plus => ['+'] | .minus => ['-'] | .star => ['*'] | .slash => ['/']
  | .ident name => '$' :: name.val
  | .numLit n => (if n.intDigits.negative then '~' else '#') :: n.chars

def Token.ofChars? (cs : List Char) : Option Token :=
  match cs with
  | ['s', 't', 'r', 'u', 'c', 't'] => some .kwStruct
  | ['f', 'n'] => some .kwFn
  | ['v', 'a', 'r'] => some .kwVar
  | ['l', 'e', 't'] => some .kwLet
  | ['r', 'e', 't', 'u', 'r', 'n'] => some .kwReturn
  | ['u', 'n', 'i', 'f', 'o', 'r', 'm'] => some .kwUniform
  | ['f', '3', '2'] => some .tyF32
  | ['i', '3', '2'] => some .tyI32
  | ['u', '3', '2'] => some .tyU32
  | ['v', 'e', 'c', '2'] => some .tyVec2
  | ['v', 'e', 'c', '3'] => some .tyVec3
  | ['v', 'e', 'c', '4'] => some .tyVec4
  | ['m', 'a', 't', '4', 'x', '4'] => some .tyMat4x4
  | ['v', 'e', 'r', 't', 'e', 'x'] => some .kwVertex
  | ['f', 'r', 'a', 'g', 'm', 'e', 'n', 't'] => some .kwFragment
  | ['c', 'o', 'm', 'p', 'u', 't', 'e'] => some .kwCompute
  | ['l', 'o', 'c', 'a', 't', 'i', 'o', 'n'] => some .kwLocation
  | ['b', 'u', 'i', 'l', 't', 'i', 'n'] => some .kwBuiltin
  | ['g', 'r', 'o', 'u', 'p'] => some .kwGroup
  | ['b', 'i', 'n', 'd', 'i', 'n', 'g'] => some .kwBinding
  | ['e', 'n', 'd'] => some .kwEnd
  | ['{'] => some .lbrace
  | ['}'] => some .rbrace
  | ['('] => some .lparen
  | [')'] => some .rparen
  | ['<'] => some .langle
  | ['>'] => some .rangle
  | [','] => some .comma
  | [';'] => some .semicolon
  | [':'] => some .colon
  | ['='] => some .equals
  | ['.'] => some .dot
  | ['-', '>'] => some .arrow
  | ['@'] => some .at
  | ['+'] => some .plus
  | ['-'] => some .minus
  | ['*'] => some .star
  | ['/'] => some .slash
  | '$' :: name => if h : identOk name = true then some (.ident ⟨name, h⟩) else none
  | '#' :: rest => (parseNumeralChars? false rest).map .numLit
  | '~' :: rest => (parseNumeralChars? true rest).map .numLit
  | _ => none

theorem Token.ofChars?_render (t : Token) : Token.ofChars? t.render = some t := by
  cases t with
  | ident name =>
      obtain ⟨cs, hcs⟩ := name
      show Token.ofChars? ('$' :: cs) = some (.ident ⟨cs, hcs⟩)
      show (if h : identOk cs = true then some (Token.ident ⟨cs, h⟩) else none) =
        some (Token.ident ⟨cs, hcs⟩)
      rw [dif_pos hcs]
  | numLit n =>
      cases hneg : n.intDigits.negative with
      | false =>
          have hr : (Token.numLit n).render = '#' :: n.chars := by
            show (if n.intDigits.negative then '~' else '#') :: n.chars = '#' :: n.chars
            rw [hneg]; rfl
          rw [hr]
          show (parseNumeralChars? false n.chars).map Token.numLit = some (Token.numLit n)
          rw [← hneg, parseNumeralChars?_chars]
          rfl
      | true =>
          have hr : (Token.numLit n).render = '~' :: n.chars := by
            show (if n.intDigits.negative then '~' else '#') :: n.chars = '~' :: n.chars
            rw [hneg]; rfl
          rw [hr]
          show (parseNumeralChars? true n.chars).map Token.numLit = some (Token.numLit n)
          rw [← hneg, parseNumeralChars?_chars]
          rfl
  | _ => rfl

/-! ## Text: tokens joined by single spaces -/

/-- Consume one token's characters from the front of a character list,
stopping at the first space (which is dropped) or at the end of the list. -/
def takeToken : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if c = ' ' then ([], rest)
      else
        let (tok, rest') := takeToken rest
        (c :: tok, rest')

theorem takeToken_nil (chars : List Char) (h : ' ' ∉ chars) : takeToken chars = (chars, []) := by
  induction chars with
  | nil => rfl
  | cons c rest ih =>
      have hc : ¬ c = ' ' := fun heq => h (heq ▸ List.mem_cons_self ..)
      have hrest : ' ' ∉ rest := fun hm => h (List.mem_cons_of_mem c hm)
      show takeToken (c :: rest) = (c :: rest, [])
      simp only [takeToken, if_neg hc, ih hrest]

theorem takeToken_space (chars rest : List Char) (h : ' ' ∉ chars) :
    takeToken (chars ++ ' ' :: rest) = (chars, rest) := by
  induction chars with
  | nil => rfl
  | cons c chars ih =>
      have hc : ¬ c = ' ' := fun heq => h (heq ▸ List.mem_cons_self ..)
      have hrest : ' ' ∉ chars := fun hm => h (List.mem_cons_of_mem c hm)
      show takeToken (c :: (chars ++ ' ' :: rest)) = (c :: chars, rest)
      simp only [takeToken, if_neg hc, ih hrest]

theorem digitChar_ne_space (d : Fin 10) : digitChar d ≠ ' ' := by
  match d with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide

theorem digitsToChars_noSpace (ds : List (Fin 10)) : ' ' ∉ digitsToChars ds := by
  induction ds with
  | nil => simp [digitsToChars]
  | cons d ds ih =>
      simp only [digitsToChars, List.map_cons, List.mem_cons]
      exact fun h => h.elim (fun heq => digitChar_ne_space d heq.symm) ih

theorem Digits.noSpace (d : Digits) : ' ' ∉ d.chars := by
  simp only [Digits.chars, List.mem_cons]
  exact fun h => h.elim (fun heq => digitChar_ne_space d.digit heq.symm) (digitsToChars_noSpace d.rest)

theorem Numeral.noSpace (n : Numeral) : ' ' ∉ n.chars := by
  obtain ⟨intDigits, fracDigits⟩ := n
  cases fracDigits with
  | none =>
      show ' ' ∉ intDigits.chars ++ ([] : List Char)
      rw [List.append_nil]
      exact Digits.noSpace intDigits
  | some p =>
      obtain ⟨fdigit, frest⟩ := p
      show ' ' ∉ intDigits.chars ++ ('.' :: digitChar fdigit :: digitsToChars frest)
      simp only [List.mem_append, List.mem_cons]
      refine fun h => h.elim (Digits.noSpace intDigits) (fun hf => ?_)
      rcases hf with hf | hf | hf
      · simp at hf
      · exact digitChar_ne_space fdigit hf.symm
      · exact digitsToChars_noSpace frest hf

theorem Token.render_noSpace (t : Token) : ' ' ∉ t.render := by
  cases t with
  | ident name =>
      show ' ' ∉ ('$' :: name.val)
      simp only [List.mem_cons]
      exact fun h => h.elim (by decide) (Name.noSpace name)
  | numLit n =>
      show ' ' ∉ (if n.intDigits.negative then '~' else '#') :: n.chars
      simp only [List.mem_cons]
      refine fun h => h.elim (fun heq => ?_) (Numeral.noSpace n)
      cases hb : n.intDigits.negative <;> rw [hb] at heq <;> simp at heq
  | _ => decide

theorem Token.render_ne_nil (t : Token) : t.render ≠ [] := by
  cases t with
  | ident name => exact List.cons_ne_nil _ _
  | numLit n => cases n.intDigits.negative <;> exact List.cons_ne_nil _ _
  | _ => decide

/-- Render a token list as space-separated text. -/
def tokensToChars : List Token → List Char
  | [] => []
  | [t] => t.render
  | t :: rest => t.render ++ ' ' :: tokensToChars rest

/-- Decode `fuel` tokens (an upper bound, not an exact count) from the front
of a character list. Plain structural recursion on `fuel`. -/
def charsToTokensFuel : Nat → List Char → Option (List Token)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, chars =>
      let (tokChars, rest) := takeToken chars
      match Token.ofChars? tokChars with
      | none => none
      | some t => (charsToTokensFuel fuel rest).map (t :: ·)

def charsToTokens (chars : List Char) : Option (List Token) := charsToTokensFuel chars.length chars

theorem charsToTokensFuel_flatMap (ts : List Token) (fuel : Nat) (hfuel : ts.length ≤ fuel) :
    charsToTokensFuel fuel (tokensToChars ts) = some ts := by
  induction ts generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons t ts ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hfuel' : ts.length ≤ fuel := by simp only [List.length_cons] at hfuel; omega
          cases ts with
          | nil =>
              show charsToTokensFuel (fuel + 1) t.render = some [t]
              have hk := takeToken_nil t.render (Token.render_noSpace t)
              obtain ⟨c, cs, hcs⟩ : ∃ c cs, t.render = c :: cs := by
                cases hr : t.render with
                | nil => exact absurd hr (Token.render_ne_nil t)
                | cons c cs => exact ⟨c, cs, rfl⟩
              have hor : Token.ofChars? (c :: cs) = some t := by rw [← hcs]; exact Token.ofChars?_render t
              rw [hcs] at hk
              rw [hcs]
              simp only [charsToTokensFuel, hk, hor, Option.map_some]
          | cons t2 ts2 =>
              show charsToTokensFuel (fuel + 1) (t.render ++ ' ' :: tokensToChars (t2 :: ts2)) = some (t :: t2 :: ts2)
              have hk := takeToken_space t.render (tokensToChars (t2 :: ts2)) (Token.render_noSpace t)
              obtain ⟨c, cs, hcs⟩ : ∃ c cs, t.render = c :: cs := by
                cases hr : t.render with
                | nil => exact absurd hr (Token.render_ne_nil t)
                | cons c cs => exact ⟨c, cs, rfl⟩
              have hor : Token.ofChars? (c :: cs) = some t := by rw [← hcs]; exact Token.ofChars?_render t
              rw [hcs, List.cons_append] at hk
              rw [hcs]
              simp only [List.cons_append, charsToTokensFuel, hk, hor, ih fuel hfuel']
              rfl

theorem charsToTokens_tokensToChars (ts : List Token) :
    charsToTokens (tokensToChars ts) = some ts := by
  have hlen : ts.length ≤ (tokensToChars ts).length := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
        cases ts with
        | nil =>
            show ([t] : List Token).length ≤ t.render.length
            simp only [List.length_cons, List.length_nil]
            have := Token.render_ne_nil t
            cases h : t.render with
            | nil => exact absurd h this
            | cons _ _ => simp
        | cons t2 ts2 =>
            show (t :: t2 :: ts2).length ≤ (t.render ++ ' ' :: tokensToChars (t2 :: ts2)).length
            simp only [List.length_cons, List.length_append]
            simp only [List.length_cons] at ih
            omega
  exact charsToTokensFuel_flatMap ts (tokensToChars ts).length hlen

/-! ## A reusable terminated-list parser

Every variable-length list in the AST below (struct fields, function
parameters, a body's statements, a call's arguments) is rendered as its
items followed by a dedicated `Token.kwEnd`, and parsed back by this one
fuel-bounded helper — proved once, applied at every list site instead of
re-proving the same induction per site. -/

/-- Parse items until `Token.kwEnd`, using at most `fuel` items (an upper
bound, not an exact count). -/
def parseListFuel {α : Type} (parseOne : List Token → Option (α × List Token)) :
    Nat → List Token → Option (List α × List Token)
  | _, Token.kwEnd :: rest => some ([], rest)
  | 0, _ => none
  | fuel + 1, ts =>
      match parseOne ts with
      | none => none
      | some (a, rest) => (parseListFuel parseOne fuel rest).map (fun ar => (a :: ar.1, ar.2))

/-- Render a list of items followed by the terminator. -/
def renderList {α : Type} (render : α → List Token) (items : List α) : List Token :=
  items.flatMap render ++ [Token.kwEnd]

/-- The generic round trip: given that `parseOne` inverts `render` (for every
item, with any trailing tokens) and that `render` never itself starts with
the terminator, `parseListFuel` inverts `renderList`. -/
theorem parseListFuel_flatMap {α : Type} (parseOne : List Token → Option (α × List Token))
    (render : α → List Token)
    (hparse : ∀ (a : α) (rest : List Token), parseOne (render a ++ rest) = some (a, rest))
    (hhead : ∀ a : α, ∃ tok toks, render a = tok :: toks ∧ tok ≠ Token.kwEnd)
    (items : List α) (tail : List Token) (fuel : Nat) (hfuel : items.length ≤ fuel) :
    parseListFuel parseOne fuel (items.flatMap render ++ (Token.kwEnd :: tail)) = some (items, tail) := by
  induction items generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons a items ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hfuel' : items.length ≤ fuel := by simp only [List.length_cons] at hfuel; omega
          show parseListFuel parseOne (fuel + 1)
            (render a ++ items.flatMap render ++ (Token.kwEnd :: tail)) = some (a :: items, tail)
          rw [List.append_assoc]
          obtain ⟨tok, toks, hrender, htok⟩ := hhead a
          have hp := hparse a (items.flatMap render ++ (Token.kwEnd :: tail))
          rw [hrender] at hp ⊢
          rw [List.cons_append] at hp
          show parseListFuel parseOne (fuel + 1) (tok :: (toks ++ (items.flatMap render ++ (Token.kwEnd :: tail)))) =
            some (a :: items, tail)
          cases tok with
          | kwEnd => exact absurd rfl htok
          | _ => simp only [parseListFuel, hp, ih fuel hfuel']; rfl

/-- Decode a whole terminated list from its rendered form. -/
def parseList {α : Type} (parseOne : List Token → Option (α × List Token)) (ts : List Token) :
    Option (List α × List Token) :=
  parseListFuel parseOne ts.length ts

theorem parseList_renderList {α : Type} (parseOne : List Token → Option (α × List Token))
    (render : α → List Token)
    (hparse : ∀ (a : α) (rest : List Token), parseOne (render a ++ rest) = some (a, rest))
    (hhead : ∀ a : α, ∃ tok toks, render a = tok :: toks ∧ tok ≠ Token.kwEnd)
    (items : List α) (tail : List Token) :
    parseList parseOne (renderList render items ++ tail) = some (items, tail) := by
  have hone : ∀ a : α, 1 ≤ (render a).length := by
    intro a
    obtain ⟨tok, toks, hrender, _⟩ := hhead a
    simp [hrender]
  have hfuel : items.length ≤ (renderList render items ++ tail).length := by
    simp only [renderList, List.length_append]
    have hflat : items.length ≤ (items.flatMap render).length := by
      induction items with
      | nil => simp
      | cons a items ih =>
          show (a :: items).length ≤ (render a ++ items.flatMap render).length
          simp only [List.length_cons, List.length_append]
          have := hone a
          omega
    omega
  have heq : renderList render items ++ tail = items.flatMap render ++ (Token.kwEnd :: tail) := by
    simp [renderList]
  show parseListFuel parseOne (renderList render items ++ tail).length (renderList render items ++ tail) =
    some (items, tail)
  rw [heq]
  rw [heq] at hfuel
  exact parseListFuel_flatMap parseOne render hparse hhead items tail _ hfuel

/-! ## Types, operators, stages -/

/-- A WGSL type this vocabulary can name. -/
inductive Ty where
  | f32 | i32 | u32 | vec2 | vec3 | vec4 | mat4x4
deriving DecidableEq, Repr

def Ty.toTokens : Ty → List Token
  | .f32 => [.tyF32] | .i32 => [.tyI32] | .u32 => [.tyU32]
  | .vec2 => [.tyVec2] | .vec3 => [.tyVec3] | .vec4 => [.tyVec4]
  | .mat4x4 => [.tyMat4x4]

def Ty.ofTokens : List Token → Option (Ty × List Token)
  | .tyF32 :: rest => some (.f32, rest)
  | .tyI32 :: rest => some (.i32, rest)
  | .tyU32 :: rest => some (.u32, rest)
  | .tyVec2 :: rest => some (.vec2, rest)
  | .tyVec3 :: rest => some (.vec3, rest)
  | .tyVec4 :: rest => some (.vec4, rest)
  | .tyMat4x4 :: rest => some (.mat4x4, rest)
  | _ => none

theorem Ty.ofTokens_toTokens (ty : Ty) (rest : List Token) :
    Ty.ofTokens (ty.toTokens ++ rest) = some (ty, rest) := by
  cases ty <;> rfl

/-- The binary operators this vocabulary applies. -/
inductive BinOp where
  | add | sub | mul | div
deriving DecidableEq, Repr

def BinOp.toTokens : BinOp → List Token
  | .add => [.plus] | .sub => [.minus] | .mul => [.star] | .div => [.slash]

def BinOp.ofTokens : List Token → Option (BinOp × List Token)
  | .plus :: rest => some (.add, rest)
  | .minus :: rest => some (.sub, rest)
  | .star :: rest => some (.mul, rest)
  | .slash :: rest => some (.div, rest)
  | _ => none

theorem BinOp.ofTokens_toTokens (op : BinOp) (rest : List Token) :
    BinOp.ofTokens (op.toTokens ++ rest) = some (op, rest) := by
  cases op <;> rfl

/-- The pipeline stage an entry point runs in. -/
inductive Stage where
  | vertex | fragment | compute
deriving DecidableEq, Repr

def Stage.toTokens : Stage → List Token
  | .vertex => [.kwVertex] | .fragment => [.kwFragment] | .compute => [.kwCompute]

def Stage.ofTokens : List Token → Option (Stage × List Token)
  | .kwVertex :: rest => some (.vertex, rest)
  | .kwFragment :: rest => some (.fragment, rest)
  | .kwCompute :: rest => some (.compute, rest)
  | _ => none

theorem Stage.ofTokens_toTokens (s : Stage) (rest : List Token) :
    Stage.ofTokens (s.toTokens ++ rest) = some (s, rest) := by
  cases s <;> rfl

/-- A struct member attribute: a pipeline `@location(n)` index, or a
`@builtin(name)` value. -/
inductive Attr where
  | location (n : Numeral)
  | builtin (name : Name)
deriving DecidableEq, Repr

def Attr.toTokens : Attr → List Token
  | .location n => [.kwLocation, .numLit n]
  | .builtin name => [.kwBuiltin, .ident name]

def Attr.ofTokens : List Token → Option (Attr × List Token)
  | .kwLocation :: .numLit n :: rest => some (.location n, rest)
  | .kwBuiltin :: .ident name :: rest => some (.builtin name, rest)
  | _ => none

theorem Attr.ofTokens_toTokens (a : Attr) (rest : List Token) :
    Attr.ofTokens (a.toTokens ++ rest) = some (a, rest) := by
  cases a <;> rfl

/-! ## Atoms and expressions

Two more departures of the same kind as the token sigils, and for the same
reason — every `ofTokens` here inverts its `toTokens` for an *arbitrary*
token suffix, so no form may be a prefix of another form's rendering:

* **Member access is `.`-prefixed** (`. $base $field`, not `$base . $field`).
  Written infix, a bare identifier atom would be a prefix of a member atom,
  and `Atom.ofTokens (Atom.ident x).toTokens ++ ts` could not be `ident x`
  for every `ts` — a `ts` beginning `. $f` would have to read as a member.
* **A call is parenthesised around its callee** (`( $f $a $b end )`) and a
  **binary application is written prefix** (`+ $a $b`). This makes the three
  expression forms decidable from their first token alone: a call opens with
  `(`, a binary application with its operator, and an atom with a numeral,
  an identifier, or the member `.`. -/

/-- A leaf value: a numeral, an identifier, or one member access. -/
inductive Atom where
  | numeral (n : Numeral)
  | ident (name : Name)
  | member (base field : Name)
deriving DecidableEq, Repr

def Atom.toTokens : Atom → List Token
  | .numeral n => [.numLit n]
  | .ident name => [.ident name]
  | .member base field => [.dot, .ident base, .ident field]

def Atom.ofTokens : List Token → Option (Atom × List Token)
  | .numLit n :: rest => some (.numeral n, rest)
  | .dot :: .ident base :: .ident field :: rest => some (.member base field, rest)
  | .ident name :: rest => some (.ident name, rest)
  | _ => none

theorem Atom.ofTokens_toTokens (a : Atom) (rest : List Token) :
    Atom.ofTokens (a.toTokens ++ rest) = some (a, rest) := by
  cases a <;> rfl

theorem Atom.head_ne_kwEnd (a : Atom) :
    ∃ tok toks, a.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd := by
  cases a <;> exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩

/-- An expression: an atom, a call of a named function on atom arguments, or
one binary operator applied to two atoms. -/
inductive Expr where
  | atom (a : Atom)
  | call (callee : Name) (args : List Atom)
  | binary (op : BinOp) (lhs rhs : Atom)
deriving DecidableEq, Repr

def Expr.toTokens : Expr → List Token
  | .atom a => a.toTokens
  | .call callee args =>
      [Token.lparen, Token.ident callee] ++ renderList Atom.toTokens args ++ [Token.rparen]
  | .binary op lhs rhs => op.toTokens ++ lhs.toTokens ++ rhs.toTokens

def Expr.ofTokens (ts : List Token) : Option (Expr × List Token) :=
  match ts with
  | .lparen :: .ident callee :: ts1 =>
      match parseList Atom.ofTokens ts1 with
      | some (args, .rparen :: rest) => some (.call callee args, rest)
      | _ => none
  | ts1 =>
      match BinOp.ofTokens ts1 with
      | some (op, ts2) =>
          match Atom.ofTokens ts2 with
          | some (lhs, ts3) =>
              match Atom.ofTokens ts3 with
              | some (rhs, rest) => some (.binary op lhs rhs, rest)
              | none => none
          | none => none
      | none => (Atom.ofTokens ts1).map (fun p => (.atom p.1, p.2))

theorem Expr.ofTokens_toTokens (e : Expr) (rest : List Token) :
    Expr.ofTokens (e.toTokens ++ rest) = some (e, rest) := by
  cases e with
  | atom a => cases a <;> rfl
  | binary op lhs rhs => cases op <;> cases lhs <;> cases rhs <;> rfl
  | call callee args =>
      have hlist := parseList_renderList Atom.ofTokens Atom.toTokens Atom.ofTokens_toTokens
        Atom.head_ne_kwEnd args (Token.rparen :: rest)
      simp only [Expr.toTokens, List.cons_append, List.nil_append, List.append_assoc,
        Expr.ofTokens, hlist]

theorem Expr.head_ne_kwEnd (e : Expr) :
    ∃ tok toks, e.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd := by
  cases e with
  | atom a => cases a <;> exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | call _ _ => exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | binary op _ _ => cases op <;> exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩

/-! ## Statements -/

/-- A statement: a `let` or `var` binding, a `return`, or an assignment to an
identifier or member. -/
inductive Stmt where
  | letStmt (name : Name) (value : Expr)
  | varStmt (name : Name) (value : Expr)
  | returnStmt (value : Expr)
  | assignStmt (target : Atom) (value : Expr)
deriving DecidableEq, Repr

def Stmt.toTokens : Stmt → List Token
  | .letStmt name value =>
      [Token.kwLet, Token.ident name, Token.equals] ++ value.toTokens ++ [Token.semicolon]
  | .varStmt name value =>
      [Token.kwVar, Token.ident name, Token.equals] ++ value.toTokens ++ [Token.semicolon]
  | .returnStmt value => [Token.kwReturn] ++ value.toTokens ++ [Token.semicolon]
  | .assignStmt target value =>
      target.toTokens ++ [Token.equals] ++ value.toTokens ++ [Token.semicolon]

/-- Parse the `= value ;` tail of an assignment whose target is already
parsed. Split out so that every arm of `Stmt.ofTokens` below matches a
literal leading token, which keeps its equation lemmas unconditional. -/
def Stmt.assignTail (target : Atom) : List Token → Option (Stmt × List Token)
  | .equals :: ts =>
      match Expr.ofTokens ts with
      | some (value, .semicolon :: rest) => some (.assignStmt target value, rest)
      | _ => none
  | _ => none

/-- Parse the `value ;` tail of a `let`/`var`/`return`, wrapped by `mk`. -/
def Stmt.valueTail (mk : Expr → Stmt) (ts : List Token) : Option (Stmt × List Token) :=
  match Expr.ofTokens ts with
  | some (value, .semicolon :: rest) => some (mk value, rest)
  | _ => none

def Stmt.ofTokens : List Token → Option (Stmt × List Token)
  | .kwLet :: .ident name :: .equals :: ts => Stmt.valueTail (Stmt.letStmt name) ts
  | .kwVar :: .ident name :: .equals :: ts => Stmt.valueTail (Stmt.varStmt name) ts
  | .kwReturn :: ts => Stmt.valueTail Stmt.returnStmt ts
  | .numLit n :: ts => Stmt.assignTail (.numeral n) ts
  | .dot :: .ident base :: .ident field :: ts => Stmt.assignTail (.member base field) ts
  | .ident name :: ts => Stmt.assignTail (.ident name) ts
  | _ => none

theorem Stmt.ofTokens_toTokens (s : Stmt) (rest : List Token) :
    Stmt.ofTokens (s.toTokens ++ rest) = some (s, rest) := by
  cases s with
  | letStmt name value =>
      simp only [Stmt.toTokens, List.cons_append, List.nil_append, List.append_assoc,
        Stmt.ofTokens, Stmt.valueTail, Expr.ofTokens_toTokens]
  | varStmt name value =>
      simp only [Stmt.toTokens, List.cons_append, List.nil_append, List.append_assoc,
        Stmt.ofTokens, Stmt.valueTail, Expr.ofTokens_toTokens]
  | returnStmt value =>
      simp only [Stmt.toTokens, List.cons_append, List.nil_append, List.append_assoc,
        Stmt.ofTokens, Stmt.valueTail, Expr.ofTokens_toTokens]
  | assignStmt target value =>
      cases target <;>
        simp only [Stmt.toTokens, Atom.toTokens, List.cons_append, List.nil_append,
          List.append_assoc, Stmt.ofTokens, Stmt.assignTail, Expr.ofTokens_toTokens]

theorem Stmt.head_ne_kwEnd (s : Stmt) :
    ∃ tok toks, s.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd := by
  cases s with
  | letStmt _ _ => exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | varStmt _ _ => exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | returnStmt _ => exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | assignStmt target _ => cases target <;> exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩

/-! ## Struct fields, function parameters, uniform bindings -/

/-- A function parameter: a name and its type. -/
structure Param where
  name : Name
  ty : Ty
deriving DecidableEq, Repr

def Param.toTokens (p : Param) : List Token := [Token.ident p.name, Token.colon] ++ p.ty.toTokens

def Param.ofTokens : List Token → Option (Param × List Token)
  | .ident name :: .colon :: ts =>
      match Ty.ofTokens ts with
      | some (ty, rest) => some ({ name, ty }, rest)
      | none => none
  | _ => none

theorem Param.ofTokens_toTokens (p : Param) (rest : List Token) :
    Param.ofTokens (p.toTokens ++ rest) = some (p, rest) := by
  obtain ⟨_, ty⟩ := p
  cases ty <;> rfl

theorem Param.head_ne_kwEnd (p : Param) :
    ∃ tok toks, p.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd :=
  ⟨_, _, rfl, fun h => Token.noConfusion h⟩

/-- A struct member: a name, a type, and an optional pipeline attribute. -/
structure Field where
  name : Name
  ty : Ty
  attr : Option Attr
deriving DecidableEq, Repr

def Field.toTokens (f : Field) : List Token :=
  (match f.attr with
    | none => []
    | some a => Token.at :: a.toTokens)
  ++ [Token.ident f.name, Token.colon] ++ f.ty.toTokens ++ [Token.semicolon]

/-- Parse the `name : ty ;` tail of a field whose attribute is already
parsed. -/
def Field.tail (attr : Option Attr) : List Token → Option (Field × List Token)
  | .ident name :: .colon :: ts =>
      match Ty.ofTokens ts with
      | some (ty, .semicolon :: rest) => some ({ name, ty, attr }, rest)
      | _ => none
  | _ => none

def Field.ofTokens : List Token → Option (Field × List Token)
  | .at :: ts =>
      match Attr.ofTokens ts with
      | some (a, ts1) => Field.tail (some a) ts1
      | none => none
  | ts => Field.tail none ts

theorem Field.ofTokens_toTokens (f : Field) (rest : List Token) :
    Field.ofTokens (f.toTokens ++ rest) = some (f, rest) := by
  obtain ⟨_, ty, attr⟩ := f
  cases attr with
  | none => cases ty <;> rfl
  | some a => cases a <;> cases ty <;> rfl

theorem Field.head_ne_kwEnd (f : Field) :
    ∃ tok toks, f.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd := by
  obtain ⟨_, _, attr⟩ := f
  cases attr <;> exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩

/-- A module-scope uniform binding: `@group(g) @binding(b) var<uniform> n : t;`. -/
structure VarDecl where
  name : Name
  group : Numeral
  binding : Numeral
  ty : Ty
deriving DecidableEq, Repr

def VarDecl.toTokens (v : VarDecl) : List Token :=
  [Token.at, Token.kwGroup, Token.lparen, Token.numLit v.group, Token.rparen,
    Token.at, Token.kwBinding, Token.lparen, Token.numLit v.binding, Token.rparen,
    Token.kwVar, Token.langle, Token.kwUniform, Token.rangle, Token.ident v.name, Token.colon]
  ++ v.ty.toTokens ++ [Token.semicolon]

def VarDecl.ofTokens : List Token → Option (VarDecl × List Token)
  | .at :: .kwGroup :: .lparen :: .numLit group :: .rparen ::
      .at :: .kwBinding :: .lparen :: .numLit binding :: .rparen ::
      .kwVar :: .langle :: .kwUniform :: .rangle :: .ident name :: .colon :: ts =>
      match Ty.ofTokens ts with
      | some (ty, .semicolon :: rest) => some ({ name, group, binding, ty }, rest)
      | _ => none
  | _ => none

theorem VarDecl.ofTokens_toTokens (v : VarDecl) (rest : List Token) :
    VarDecl.ofTokens (v.toTokens ++ rest) = some (v, rest) := by
  obtain ⟨_, _, _, ty⟩ := v
  cases ty <;> rfl

/-! ## Function declarations -/

/-- A function: an optional stage attribute (what makes it an entry point),
its parameters, an optional return type, and its body. -/
structure FnDecl where
  name : Name
  stage : Option Stage
  params : List Param
  returnTy : Option Ty
  body : List Stmt
deriving DecidableEq, Repr

def FnDecl.toTokens (f : FnDecl) : List Token :=
  (match f.stage with
    | none => []
    | some s => Token.at :: s.toTokens)
  ++ [Token.kwFn, Token.ident f.name, Token.lparen]
  ++ renderList Param.toTokens f.params
  ++ [Token.rparen]
  ++ (match f.returnTy with
    | none => []
    | some t => Token.arrow :: t.toTokens)
  ++ [Token.lbrace]
  ++ renderList Stmt.toTokens f.body
  ++ [Token.rbrace]

/-- Parse a body `{ … }` and assemble the function, given everything that
precedes it. -/
def FnDecl.bodyTail (name : Name) (stage : Option Stage) (params : List Param)
    (returnTy : Option Ty) : List Token → Option (FnDecl × List Token)
  | .lbrace :: ts =>
      match parseList Stmt.ofTokens ts with
      | some (body, .rbrace :: rest) => some ({ name, stage, params, returnTy, body }, rest)
      | _ => none
  | _ => none

/-- Parse everything after the opening `(` of a function's parameter list. -/
def FnDecl.paramsTail (name : Name) (stage : Option Stage) (ts : List Token) :
    Option (FnDecl × List Token) :=
  match parseList Param.ofTokens ts with
  | some (params, .rparen :: ts1) =>
      match ts1 with
      | .arrow :: ts2 =>
          match Ty.ofTokens ts2 with
          | some (ty, ts3) => FnDecl.bodyTail name stage params (some ty) ts3
          | none => none
      | ts2 => FnDecl.bodyTail name stage params none ts2
  | _ => none

def FnDecl.ofTokens : List Token → Option (FnDecl × List Token)
  | .at :: .kwVertex :: .kwFn :: .ident name :: .lparen :: ts =>
      FnDecl.paramsTail name (some .vertex) ts
  | .at :: .kwFragment :: .kwFn :: .ident name :: .lparen :: ts =>
      FnDecl.paramsTail name (some .fragment) ts
  | .at :: .kwCompute :: .kwFn :: .ident name :: .lparen :: ts =>
      FnDecl.paramsTail name (some .compute) ts
  | .kwFn :: .ident name :: .lparen :: ts => FnDecl.paramsTail name none ts
  | _ => none

theorem FnDecl.ofTokens_toTokens (f : FnDecl) (rest : List Token) :
    FnDecl.ofTokens (f.toTokens ++ rest) = some (f, rest) := by
  obtain ⟨name, stage, params, returnTy, body⟩ := f
  have hparams : ∀ tail : List Token,
      parseList Param.ofTokens (renderList Param.toTokens params ++ tail) = some (params, tail) :=
    fun tail => parseList_renderList Param.ofTokens Param.toTokens Param.ofTokens_toTokens
      Param.head_ne_kwEnd params tail
  have hbody : ∀ tail : List Token,
      parseList Stmt.ofTokens (renderList Stmt.toTokens body ++ tail) = some (body, tail) :=
    fun tail => parseList_renderList Stmt.ofTokens Stmt.toTokens Stmt.ofTokens_toTokens
      Stmt.head_ne_kwEnd body tail
  cases stage with
  | none =>
      cases returnTy <;>
        simp only [FnDecl.toTokens, List.cons_append, List.nil_append, List.append_assoc,
          FnDecl.ofTokens, FnDecl.paramsTail, FnDecl.bodyTail, hparams, hbody,
          Ty.ofTokens_toTokens]
  | some s =>
      cases s <;> cases returnTy <;>
        simp only [FnDecl.toTokens, Stage.toTokens, List.cons_append, List.nil_append,
          List.append_assoc, FnDecl.ofTokens, FnDecl.paramsTail, FnDecl.bodyTail, hparams, hbody,
          Ty.ofTokens_toTokens]

theorem FnDecl.head_ne_kwEnd (f : FnDecl) :
    ∃ tok toks, f.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd := by
  obtain ⟨_, stage, _, _, _⟩ := f
  cases stage <;> exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩

/-! ## Declarations and the module -/

/-- A module-scope declaration. -/
inductive Decl where
  | structDecl (name : Name) (fields : List Field)
  | varDecl (v : VarDecl)
  | fnDecl (f : FnDecl)
deriving DecidableEq, Repr

def Decl.toTokens : Decl → List Token
  | .structDecl name fields =>
      [Token.kwStruct, Token.ident name, Token.lbrace]
      ++ renderList Field.toTokens fields ++ [Token.rbrace]
  | .varDecl v => v.toTokens
  | .fnDecl f => f.toTokens

/-- A `varDecl` and a stage-attributed `fnDecl` both open with `@`, so the
dispatch below looks at the second token: `@ group …` is the uniform
binding, and every other `@` opens a function's stage attribute. -/
def Decl.ofTokens : List Token → Option (Decl × List Token)
  | .kwStruct :: .ident name :: .lbrace :: ts =>
      match parseList Field.ofTokens ts with
      | some (fields, .rbrace :: rest) => some (.structDecl name fields, rest)
      | _ => none
  | ts@(.at :: .kwGroup :: _) => (VarDecl.ofTokens ts).map (fun p => (.varDecl p.1, p.2))
  | ts => (FnDecl.ofTokens ts).map (fun p => (.fnDecl p.1, p.2))

theorem Decl.ofTokens_toTokens (d : Decl) (rest : List Token) :
    Decl.ofTokens (d.toTokens ++ rest) = some (d, rest) := by
  cases d with
  | structDecl name fields =>
      have hfields : ∀ tail : List Token,
          parseList Field.ofTokens (renderList Field.toTokens fields ++ tail) =
            some (fields, tail) :=
        fun tail => parseList_renderList Field.ofTokens Field.toTokens Field.ofTokens_toTokens
          Field.head_ne_kwEnd fields tail
      simp only [Decl.toTokens, List.cons_append, List.nil_append, List.append_assoc,
        Decl.ofTokens, hfields]
  | varDecl v =>
      obtain ⟨name, group, binding, ty⟩ := v
      simp only [Decl.toTokens, VarDecl.toTokens, List.cons_append, List.nil_append,
        List.append_assoc, Decl.ofTokens]
      rw [show (Token.at :: Token.kwGroup :: Token.lparen :: Token.numLit group :: Token.rparen ::
          Token.at :: Token.kwBinding :: Token.lparen :: Token.numLit binding :: Token.rparen ::
          Token.kwVar :: Token.langle :: Token.kwUniform :: Token.rangle :: Token.ident name ::
          Token.colon :: (Ty.toTokens ty ++ (Token.semicolon :: rest))) =
        VarDecl.toTokens { name, group, binding, ty } ++ rest from by
          simp only [VarDecl.toTokens, List.cons_append, List.nil_append, List.append_assoc],
        VarDecl.ofTokens_toTokens]
      rfl
  | fnDecl f =>
      obtain ⟨name, stage, params, returnTy, body⟩ := f
      have hfn := FnDecl.ofTokens_toTokens { name, stage, params, returnTy, body } rest
      cases stage with
      | none =>
          simp only [Decl.toTokens, FnDecl.toTokens, List.cons_append, List.nil_append,
            List.append_assoc] at hfn ⊢
          simp only [Decl.ofTokens, hfn, Option.map_some]
      | some s =>
          cases s <;>
            (simp only [Decl.toTokens, FnDecl.toTokens, Stage.toTokens, List.cons_append,
                List.nil_append, List.append_assoc] at hfn ⊢
             simp only [Decl.ofTokens, hfn, Option.map_some])

theorem Decl.head_ne_kwEnd (d : Decl) :
    ∃ tok toks, d.toTokens = tok :: toks ∧ tok ≠ Token.kwEnd := by
  cases d with
  | structDecl _ _ => exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | varDecl _ => exact ⟨_, _, rfl, fun h => Token.noConfusion h⟩
  | fnDecl f => exact FnDecl.head_ne_kwEnd f

/-! ## Bytes: the module's text as UTF-8

The seam's encoding boundary is `List UInt8`, so the character list a module
renders to becomes a `String` and then its UTF-8 bytes — the same
`String.fromUTF8?`-based boundary `Grass.Shader.SPIRV.Module.bytesToString?`
uses for the strings inside a SPIR-V `OpEntryPoint`. A `String` built from a
`List Char` is always valid UTF-8, so the decode direction never fails on
bytes this encoder produced. -/

def charsToBytes (cs : List Char) : List UInt8 := (String.ofList cs).toUTF8.data.toList

def bytesToChars? (bytes : List UInt8) : Option (List Char) :=
  (String.fromUTF8? (ByteArray.mk bytes.toArray)).map String.toList

theorem bytesToChars?_charsToBytes (cs : List Char) :
    bytesToChars? (charsToBytes cs) = some cs := by
  have hstr : String.fromUTF8? (ByteArray.mk (String.ofList cs).toUTF8.data.toList.toArray) =
      some (String.ofList cs) := by
    rw [show ByteArray.mk (String.ofList cs).toUTF8.data.toList.toArray = (String.ofList cs).toUTF8
      from by simp]
    unfold String.fromUTF8?
    rw [String.toUTF8_eq_toByteArray, dif_pos (String.ofList cs).isValidUTF8]
    rfl
  simp only [bytesToChars?, charsToBytes, hstr, Option.map_some, String.toList_ofList]

/-! ## The module

A module is its declaration list. The top level reuses the same terminated
list machinery as every inner list, so the whole text ends with the `end`
token and decoding requires the token stream to be exactly consumed. -/

/-- A whole WGSL module: its module-scope declarations, in order. -/
structure Module where
  decls : List Decl
deriving DecidableEq, Repr

def Module.toTokens (m : Module) : List Token := renderList Decl.toTokens m.decls

/-- Canonical encoding: the module's space-separated token text, as UTF-8. -/
def Module.encode (m : Module) : List UInt8 := charsToBytes (tokensToChars m.toTokens)

/-- Recover a module from its bytes: UTF-8 to characters, characters to
tokens, tokens to declarations, with nothing left over. -/
def Module.decode (bytes : List UInt8) : Option Module :=
  match bytesToChars? bytes with
  | none => none
  | some cs =>
      match charsToTokens cs with
      | none => none
      | some ts =>
          match parseList Decl.ofTokens ts with
          | some (decls, []) => some { decls }
          | _ => none

/-- `Grass.Target.ShaderLanguage.decode_encode` for WGSL. -/
theorem Module.decode_encode (m : Module) : Module.decode (Module.encode m) = some m := by
  obtain ⟨decls⟩ := m
  have hdecls := parseList_renderList Decl.ofTokens Decl.toTokens Decl.ofTokens_toTokens
    Decl.head_ne_kwEnd decls []
  rw [List.append_nil] at hdecls
  simp only [Module.decode, Module.encode, Module.toTokens, bytesToChars?_charsToBytes,
    charsToTokens_tokensToChars, hdecls]

/-! ## Entry points and stages -/

/-- An entry point: the name of a function carrying a stage attribute, and
the stage it runs in. Unlike SPIR-V, where `OpEntryPoint` names a function by
result id, a WGSL entry point *is* the attributed function, so the entry's
name is the function's own name. -/
structure Entry where
  name : Name
  stage : Stage
deriving DecidableEq, Repr

/-- The entry points a module declares: its stage-attributed functions. -/
def Module.entries (m : Module) : List Entry :=
  m.decls.filterMap fun d => match d with
    | .fnDecl f => f.stage.map fun stage => { name := f.name, stage }
    | _ => none

end Grass.Shader.WGSL.Module
