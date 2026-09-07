import Grass.Construct.Report
import Tests.Construct.SourceAst

/-!
# Construction report fixtures

Fixtures accept exact ordered residual keys and reject reordered phases,
duplicate keys, missing allowlist entries, and extra allowlist entries.
-/

namespace Grass.Tests.Construct.Report

open Grass Grass.CFG Grass.Construct Grass.Construct.Fragment
open Grass.Tests.Construct.SourceAst

def key (phase : Phase) (name : String) : ResidualKey where
  block := some (blockId "first")
  origin := some ⟨[fragmentId "pair"], [], 0⟩
  edge := some (exitTag "done")
  phase := phase
  subject := ⟨"test.report", name⟩

def symbolic : Residual := ⟨key .symbolic "transition", True⟩
def frame : Residual := ⟨key .frame "preservation", True⟩

def accepted : ResidualReport where
  residuals := [symbolic, frame]
  reviewedAllowlist := [symbolic.key, frame.key]

example : accepted.WellFormed := by decide

def reordered : ResidualReport where
  residuals := [frame, symbolic]
  reviewedAllowlist := [frame.key, symbolic.key]

example : ¬ reordered.WellFormed := by decide

def duplicate : ResidualReport where
  residuals := [symbolic, symbolic]
  reviewedAllowlist := [symbolic.key, symbolic.key]

example : ¬ duplicate.WellFormed := by decide

def missing : ResidualReport where
  residuals := [symbolic, frame]
  reviewedAllowlist := [symbolic.key]

example : ¬ missing.WellFormed := by decide

def extra : ResidualReport where
  residuals := [symbolic]
  reviewedAllowlist := [symbolic.key, frame.key]

example : ¬ extra.WellFormed := by decide

end Grass.Tests.Construct.Report
