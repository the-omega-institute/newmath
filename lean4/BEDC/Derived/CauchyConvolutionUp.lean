import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyConvolutionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyConvolutionPacket [AskSetup] [PackageSetup]
    (leftSeries rightSeries convolution prefixRow tailBudget handoff sealRow transports routes
      provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftSeries ∧ UnaryHistory rightSeries ∧ UnaryHistory convolution ∧
    UnaryHistory prefixRow ∧ UnaryHistory tailBudget ∧ UnaryHistory handoff ∧
      UnaryHistory sealRow ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont leftSeries rightSeries convolution ∧
          Cont convolution prefixRow tailBudget ∧ Cont tailBudget handoff sealRow ∧
            PkgSig bundle sealRow pkg

theorem CauchyConvolutionPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {leftSeries rightSeries convolution prefixRow tailBudget handoff sealRow transports routes
      provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff sealRow
        transports routes provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff
              sealRow transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff
              sealRow transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff
              sealRow transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyConvolutionUp
