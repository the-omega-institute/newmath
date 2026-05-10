import BEDC.Derived.CurvatureUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureChernWeilSourceEnvelope_semantic_name_certificate [AskSetup] [PackageSetup]
    {curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger classifier
        bundle pkg ->
      SemanticNameCert
        (fun target : BHist =>
          exists carriedProvenance : BHist,
            CurvatureChernWeilSourceEnvelope curvatureLedger derham carriedProvenance
              connectionLedger target bundle pkg)
        (fun target : BHist =>
          exists carriedProvenance : BHist,
            CurvatureChernWeilSourceEnvelope curvatureLedger derham carriedProvenance
              connectionLedger target bundle pkg)
        (fun target : BHist =>
          exists carriedProvenance : BHist,
            CurvatureChernWeilSourceEnvelope curvatureLedger derham carriedProvenance
              connectionLedger target bundle pkg)
        (fun left right : BHist =>
          (exists lp : BHist,
            CurvatureChernWeilSourceEnvelope curvatureLedger derham lp connectionLedger left
              bundle pkg) /\
            (exists rp : BHist,
              CurvatureChernWeilSourceEnvelope curvatureLedger derham rp connectionLedger right
                bundle pkg) /\
              hsame left right) := by
  intro envelope
  constructor
  · constructor
    · exact Exists.intro classifier (Exists.intro provenance envelope)
    · intro h source
      exact And.intro source (And.intro source (hsame_refl h))
    · intro h k same
      exact And.intro same.right.left (And.intro same.left (hsame_symm same.right.right))
    · intro h k r sameHK sameKR
      exact And.intro sameHK.left
        (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
    · intro h k same _
      exact same.right.left
  · intro h source
    exact source
  · intro h source
    exact source

theorem CurvatureChernWeilSourceEnvelope_visible_class_boundary [AskSetup] [PackageSetup]
    {curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger classifier
        bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row curvatureLedger)
          (fun row : BHist => hsame row curvatureLedger)
          (fun row : BHist => hsame row curvatureLedger) hsame ∧
        UnaryHistory curvatureLedger ∧ Cont curvatureLedger derham provenance ∧
          Cont provenance connectionLedger classifier ∧ PkgSig bundle classifier pkg := by
  intro envelope
  have cert :
      SemanticNameCert (fun row : BHist => hsame row curvatureLedger)
          (fun row : BHist => hsame row curvatureLedger)
          (fun row : BHist => hsame row curvatureLedger) hsame := {
    core := {
      carrier_inhabited := Exists.intro curvatureLedger (hsame_refl curvatureLedger)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro envelope.left
      (And.intro envelope.right.right.right.right.right.left
        (And.intro envelope.right.right.right.right.right.right.left
          envelope.right.right.right.right.right.right.right.right)))

end BEDC.Derived.CurvatureUp
