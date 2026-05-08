import BEDC.Derived.GaloisGroupUp

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem GaloisGroupAutomorphismActionPacket_fixed_base_classifier_public_surface
    [AskSetup] [PackageSetup]
    {galoisExt group fixedBase fixedBase' action action' composition inverse classifier
      classifier' provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      hsame fixedBase fixedBase' ->
        hsame action action' ->
          Cont fixedBase' action' classifier' ->
            UnaryHistory fixedBase' ∧ UnaryHistory action' ∧ UnaryHistory classifier' ∧
              hsame classifier classifier' ∧ hsame endpoint (append provenance ledger) ∧
                PkgSig bundle endpoint pkg := by
  intro packet sameFixedBase sameAction classifierCont'
  have classifierRows :=
    GaloisGroupAutomorphismActionPacket_fixed_base_classifier packet sameFixedBase sameAction
      classifierCont'
  have packetRows :=
    GaloisGroupAutomorphismActionPacket_fixed_base_carrier_obligation packet
  exact And.intro classifierRows.left
    (And.intro classifierRows.right.left
      (And.intro classifierRows.right.right.left
        (And.intro classifierRows.right.right.right
          (And.intro packetRows.right.right.right.right.right.right.right.left
            packetRows.right.right.right.right.right.right.right.right))))

end BEDC.Derived.GaloisGroupUp
