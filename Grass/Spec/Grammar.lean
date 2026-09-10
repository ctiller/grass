import Grass.Grammar.Core

/-!
# Specification-authoring facade: grammar

A thin re-export module, near-empty this round. `Grass/Grammar/*.lean` owns
the generic typed grammar vocabulary (`docs/GRAMMAR.md`); it does not yet
expose the byte-format authoring surface `Spikes/2_Sort/Spec.lean` and
`Spikes/3_Gzip/Spec.lean` need (`ByteLineFormat`, `ByteStringOrder`,
`Format (Vec ByteArray)`, `Gzip.Member`/`Gzip.memberFormat`,
`Console.byteLineStreamFormat`, `Format.parserRequirement`). Adding those is
future work under `Grass/Grammar/*.lean`, re-exported here the same way the
console facade re-exports `Grass/Console/*.lean`.
-/
