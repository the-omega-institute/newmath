import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HypergeometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HypergeometricBHistSourcePacket [AskSetup] [PackageSetup]
    (complex gamma numerator denominator ratio readback provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory complex ∧ UnaryHistory gamma ∧ UnaryHistory numerator ∧
    UnaryHistory denominator ∧ UnaryHistory readback ∧ UnaryHistory provenance ∧
      Cont numerator denominator ratio ∧ Cont ratio readback ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem HypergeometricBHistSourcePacket_root_stability [AskSetup] [PackageSetup]
    {complex gamma numerator denominator ratio readback provenance ledger endpoint numerator'
      denominator' ratio' readback' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator ratio readback
        provenance ledger endpoint bundle pkg ->
      hsame numerator numerator' ->
      hsame denominator denominator' ->
      hsame readback readback' ->
      Cont numerator' denominator' ratio' ->
      Cont ratio' readback' ledger' ->
      Cont provenance ledger' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      HypergeometricBHistSourcePacket complex gamma numerator' denominator' ratio' readback'
          provenance ledger' endpoint' bundle pkg ∧
        hsame ratio ratio' ∧ hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameNumerator sameDenominator sameReadback ratioRow' ledgerRow' endpointRow'
    pkgSig'
  have sameRatio : hsame ratio ratio' :=
    cont_respects_hsame sameNumerator sameDenominator
      packet.right.right.right.right.right.right.left ratioRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameRatio sameReadback
      packet.right.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameLedger
      packet.right.right.right.right.right.right.right.right.left endpointRow'
  exact
    ⟨⟨packet.left, packet.right.left,
        unary_transport packet.right.right.left sameNumerator,
        unary_transport packet.right.right.right.left sameDenominator,
        unary_transport packet.right.right.right.right.left sameReadback,
        packet.right.right.right.right.right.left, ratioRow', ledgerRow', endpointRow',
        pkgSig'⟩,
      sameRatio, sameLedger, sameEndpoint⟩

end BEDC.Derived.HypergeometricUp
