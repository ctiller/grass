#!/usr/bin/env bash
# Builds the injected-fault corpora the equivalence comparison runs over.
#
#   faults.sh <corpus-dir> <output-dir>
#
# Each output carries exactly one named defect in an otherwise real corpus, and
# each is chosen so that the tool is *obliged* to complain about it. That is the
# point: a comparison that only ever watches two clean runs agree has not been
# shown to be capable of disagreeing, which is the same defect
# `docs/VALIDATION.md` section 7's ratchet exists to prevent one level up.
#
# The byte-column edits are the interesting ones. Each of these tools guards its
# corpus with a digest that deliberately covers only the *coverage* columns --
# the ones saying what is exercised -- and not the columns holding what Grass
# emitted, so that an encoder change goes to the oracle that can judge it rather
# than tripping a constant-update prompt. Editing a byte column therefore passes
# the digest and reaches NASM, NDISASM or the processor, which is exactly the
# shape of the defect these tools exist to catch.
#
# Every field index below is 1-based, as `awk` counts them.
set -euo pipefail
C="$1"; F="$2"
mkdir -p "$F"

# --- x86-nasm-differential: <bytes>\t<nasm source> -------------------------
# A corrupted encoding. Field 1 is what Grass emitted; field 2 is the coverage
# the digest hashes, so this survives the digest and NASM has to notice it.
awk 'BEGIN{FS=OFS="\t"} NR==1{ $1 = "ff" substr($1,3) } {print}' \
  "$C/corpus.txt" > "$F/corpus.badbytes.txt"
# A shrunk corpus. The row-count ratchet runs before the digest here.
head -20 "$C/corpus.txt" > "$F/corpus.short.txt"
# A tampered coverage column: the digest must notice.
awk 'BEGIN{FS=OFS="\t"} NR==1{ $2 = $2 " ; tampered" } {print}' \
  "$C/corpus.txt" > "$F/corpus.baddigest.txt"
# Nothing at all -- the case a silently failing generator produces.
: > "$F/corpus.empty.txt"

# --- x86-ndisasm-differential: <bytes>\t<target>\t<text>\t<label> ----------
# A corrupted RIP-relative encoding: the target NDISASM computes must move.
awk 'BEGIN{FS=OFS="\t"} NR==1{ $1 = substr($1,1,length($1)-2) "ff" } {print}' \
  "$C/rip.txt" > "$F/rip.badbytes.txt"
# Three fields where four are required.
{ head -1 "$C/rip.txt" | cut -f1-3; tail -n +2 "$C/rip.txt"; } \
  > "$F/rip.malformed.txt"
head -3 "$C/rip.txt" > "$F/rip.short.txt"
awk 'BEGIN{FS=OFS="\t"} NR==1{ $4 = $4 " tampered" } {print}' \
  "$C/rip.txt" > "$F/rip.baddigest.txt"

# --- x86-decode-differential: <24-byte window>\t<length>\t<label> ----------
# A wrong decoded length. The window bytes are untouched, so it is NDISASM's own
# instruction boundary that contradicts the number.
awk 'BEGIN{FS=OFS="\t"} NR==1{ $2 = $2 + 1 } {print}' \
  "$C/decode.txt" > "$F/decode.badlen.txt"
# A window that is not the size the tool and the corpus agreed on.
awk 'BEGIN{FS=OFS="\t"} NR==1{ $1 = substr($1,1,length($1)-2) } {print}' \
  "$C/decode.txt" > "$F/decode.badwindow.txt"
# This tool checks the digest before the row count, so a shrunk corpus is
# reported as a digest mismatch rather than as a coverage reduction. Both
# implementations do it in that order; the case is kept because the comparison
# is of what they say, not of which guard fires.
head -100 "$C/decode.txt" > "$F/decode.short.txt"
awk 'BEGIN{FS=OFS="\t"} NR==1{ $3 = $3 " tampered" } {print}' \
  "$C/decode.txt" > "$F/decode.baddigest.txt"

# --- x86-machine-probe ------------------------------------------------------
# <label>\t<bytes>\t<before>\t<after>\t<kind>\t<note>\t<flags in>\t<flags out>
# A wrong predicted register file. Field 4 is the model's prediction and is not
# in the digest's coverage, so the processor is what contradicts it.
awk 'BEGIN{FS=OFS="\t"} NR==1{ n=split($4,a,","); a[1]="0123456789abcdef";
     s=a[1]; for(i=2;i<=n;i++) s=s "," a[i]; $4=s } {print}' \
  "$C/probes.txt" > "$F/probes.badafter.txt"
head -5 "$C/probes.txt" > "$F/probes.short.txt"
awk 'BEGIN{FS=OFS="\t"} NR==1{ $1 = $1 " tampered" } {print}' \
  "$C/probes.txt" > "$F/probes.baddigest.txt"
{ head -1 "$C/probes.txt" | cut -f1-7; tail -n +2 "$C/probes.txt"; } \
  > "$F/probes.malformed.txt"

echo "injected-fault corpora:"
for f in "$F"/*.txt; do
  printf '  %-28s %8s bytes  %6s rows\n' \
    "$(basename "$f")" "$(wc -c < "$f")" "$(wc -l < "$f")"
done
