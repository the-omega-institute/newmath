import BEDC.Derived.GaloisExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.SeparableExtUp

theorem GaloisExtSourcePacket_separability_obligation_row [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
          separable bundle pkg ∧
        UnaryHistory separability ∧ hsame classifier (append normality separability) ∧
          hsame endpoint (append provenance classifier) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.right.left
      (And.intro packet.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.left
          packet.right.right.right.right.right.right)))

end BEDC.Derived.GaloisExtUp
