import LeanChecker

-- This IO driver is separate from the mathematical proof imports. It invokes
-- complete-environment replay using the pinned Lean kernel after local builds.
unsafe def replayReviewedAllWidthFinal : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let target := `RowmotionSharpAllWidthFinalReviewed
  IO.println s!"Target: {target}; object: {← Lean.findOLean target}"
  replayFromFresh target
  IO.println "PASS: complete imported environment replayed into a fresh kernel"

#eval replayReviewedAllWidthFinal
