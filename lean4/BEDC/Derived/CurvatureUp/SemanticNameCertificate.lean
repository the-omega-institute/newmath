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

end BEDC.Derived.CurvatureUp
