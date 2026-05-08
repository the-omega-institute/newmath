import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CurvatureChernWeilSourceEnvelope_exactness [AskSetup] [PackageSetup]
    {curvature derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          exists c p : BHist,
            CurvatureChernWeilSourceEnvelope curvature derham p connectionLedger c bundle pkg ∧
              hsame row c)
        (fun row : BHist =>
          exists c p : BHist,
            CurvatureChernWeilSourceEnvelope curvature derham p connectionLedger c bundle pkg ∧
              hsame row c)
        (fun row : BHist =>
          exists c p : BHist,
            CurvatureChernWeilSourceEnvelope curvature derham p connectionLedger c bundle pkg ∧
              hsame row c)
        (fun left right : BHist =>
          (exists lc lp : BHist,
            CurvatureChernWeilSourceEnvelope curvature derham lp connectionLedger lc bundle pkg ∧
              hsame left lc) ∧
            (exists rc rp : BHist,
              CurvatureChernWeilSourceEnvelope curvature derham rp connectionLedger rc bundle pkg ∧
                hsame right rc) ∧
              hsame left right) := by
  intro envelope
  let Carrier : BHist -> Prop :=
    fun row : BHist =>
      exists c p : BHist,
        CurvatureChernWeilSourceEnvelope curvature derham p connectionLedger c bundle pkg ∧
          hsame row c
  let Classifier : BHist -> BHist -> Prop :=
    fun left right : BHist =>
      Carrier left ∧ Carrier right ∧ hsame left right
  have core : NameCert Carrier Classifier := {
    carrier_inhabited :=
      Exists.intro classifier
        (Exists.intro classifier
          (Exists.intro provenance (And.intro envelope (hsame_refl classifier))))
    equiv_refl := by
      intro row rowCarrier
      exact And.intro rowCarrier (And.intro rowCarrier (hsame_refl row))
    equiv_symm := by
      intro left right classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    equiv_trans := by
      intro left mid right classifiedLeft classifiedRight
      exact And.intro classifiedLeft.left
        (And.intro classifiedRight.right.left
          (hsame_trans classifiedLeft.right.right classifiedRight.right.right))
    carrier_respects_equiv := by
      intro left right classified _leftCarrier
      exact classified.right.left
  }
  exact {
    core := core
    pattern_sound := by
      intro row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro row rowCarrier
      exact rowCarrier
  }

end BEDC.Derived.CurvatureUp
