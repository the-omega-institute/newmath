import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HypergeometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HypergeometricBHistSourcePacket [AskSetup] [PackageSetup]
    (complex gamma numerator denominator coeff readback provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory complex ∧ UnaryHistory gamma ∧ UnaryHistory numerator ∧
    UnaryHistory denominator ∧ UnaryHistory readback ∧ UnaryHistory provenance ∧
      Cont numerator denominator coeff ∧ Cont coeff readback ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem HypergeometricBHistSourcePacket_root_carrier [AskSetup] [PackageSetup]
    {complex gamma numerator denominator coeff readback provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator coeff readback
        provenance ledger endpoint bundle pkg ->
      UnaryHistory complex ∧ UnaryHistory gamma ∧ UnaryHistory numerator ∧
        UnaryHistory denominator ∧ UnaryHistory coeff ∧ UnaryHistory readback ∧
          UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont numerator denominator coeff ∧
            Cont coeff readback ledger ∧ hsame ledger (append coeff readback) ∧
              PkgSig bundle endpoint pkg := by
  intro packet
  have numeratorUnary : UnaryHistory numerator := packet.right.right.left
  have denominatorUnary : UnaryHistory denominator := packet.right.right.right.left
  have coeffUnary : UnaryHistory coeff :=
    unary_cont_closed numeratorUnary denominatorUnary
      packet.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback := packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed coeffUnary readbackUnary packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, numeratorUnary, denominatorUnary, coeffUnary,
      readbackUnary, ledgerUnary, endpointUnary, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

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

theorem HypergeometricBHistSourcePacket_root_classifier [AskSetup] [PackageSetup]
    {complex complex' gamma gamma' numerator numerator' denominator denominator' coeff coeff'
      readback readback' provenance provenance' ledger ledger' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator coeff readback provenance
        ledger endpoint bundle pkg ->
      hsame complex complex' ->
        hsame gamma gamma' ->
          hsame numerator numerator' ->
            hsame denominator denominator' ->
              hsame readback readback' ->
                hsame provenance provenance' ->
                  Cont numerator' denominator' coeff' ->
                    Cont coeff' readback' ledger' ->
                      Cont provenance' ledger' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          HypergeometricBHistSourcePacket complex' gamma' numerator' denominator'
                              coeff' readback' provenance' ledger' endpoint' bundle pkg ∧
                            hsame coeff coeff' ∧ hsame ledger ledger' ∧
                              hsame endpoint endpoint' := by
  intro packet sameComplex sameGamma sameNumerator sameDenominator sameReadback sameProvenance
    coeffRow' ledgerRow' endpointRow' pkgSig'
  have sameCoeff : hsame coeff coeff' :=
    cont_respects_hsame sameNumerator sameDenominator
      packet.right.right.right.right.right.right.left coeffRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameCoeff sameReadback
      packet.right.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      packet.right.right.right.right.right.right.right.right.left endpointRow'
  exact
    ⟨⟨unary_transport packet.left sameComplex,
        unary_transport packet.right.left sameGamma,
        unary_transport packet.right.right.left sameNumerator,
        unary_transport packet.right.right.right.left sameDenominator,
        unary_transport packet.right.right.right.right.left sameReadback,
        unary_transport packet.right.right.right.right.right.left sameProvenance,
        coeffRow', ledgerRow', endpointRow', pkgSig'⟩,
      sameCoeff, sameLedger, sameEndpoint⟩

theorem HypergeometricBHistSourcePacket_root_ledger [AskSetup] [PackageSetup]
    {complex gamma numerator denominator coeff readback provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator coeff readback
        provenance ledger endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        Cont numerator denominator coeff ∧ Cont coeff readback ledger ∧
          Cont provenance ledger endpoint ∧ hsame ledger (append coeff readback) ∧
            hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have numeratorUnary : UnaryHistory numerator := packet.right.right.left
  have denominatorUnary : UnaryHistory denominator := packet.right.right.right.left
  have coeffUnary : UnaryHistory coeff :=
    unary_cont_closed numeratorUnary denominatorUnary
      packet.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback := packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed coeffUnary readbackUnary packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨provenanceUnary, ledgerUnary, endpointUnary,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

theorem HypergeometricBHistSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {complex gamma numerator denominator coeff readback provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator coeff readback provenance
        ledger endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont numerator denominator coeff ∧
          Cont coeff readback ledger ∧ Cont provenance ledger endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have rows := HypergeometricBHistSourcePacket_root_ledger packet
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
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
  exact
    ⟨cert, rows.right.left, rows.right.right.left, rows.right.right.right.left,
      rows.right.right.right.right.left, rows.right.right.right.right.right.left,
      rows.right.right.right.right.right.right.right.right⟩

theorem HypergeometricBHistSourcePacket_signature_gap_boundary [AskSetup] [PackageSetup]
    {complex gamma numerator denominator coeff readback provenance ledger endpoint gap : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator coeff readback provenance
        ledger endpoint bundle pkg ->
      Cont endpoint ledger gap ->
        UnaryHistory gap ∧ hsame gap (append endpoint ledger) ∧
          hsame ledger (append coeff readback) ∧ hsame endpoint (append provenance ledger) ∧
            PkgSig bundle endpoint pkg := by
  intro packet gapRow
  have rows := HypergeometricBHistSourcePacket_root_ledger packet
  have gapUnary : UnaryHistory gap :=
    unary_cont_closed rows.right.right.left rows.right.left gapRow
  exact
    ⟨gapUnary, gapRow, rows.right.right.right.right.right.right.left,
      rows.right.right.right.right.right.right.right.left,
      rows.right.right.right.right.right.right.right.right⟩

theorem HypergeometricBHistSourcePacket_root_consumer_boundary [AskSetup] [PackageSetup]
    {complex gamma numerator denominator coeff readback provenance ledger endpoint consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HypergeometricBHistSourcePacket complex gamma numerator denominator coeff readback
        provenance ledger endpoint bundle pkg ->
      Cont endpoint provenance consumer ->
      UnaryHistory consumer ∧ hsame consumer (append endpoint provenance) ∧
        hsame endpoint (append provenance ledger) ∧ hsame ledger (append coeff readback) ∧
          PkgSig bundle endpoint pkg := by
  intro packet consumerCont
  have ledgerRows :=
    HypergeometricBHistSourcePacket_root_ledger packet
  have provenanceUnary : UnaryHistory provenance := ledgerRows.left
  have endpointUnary : UnaryHistory endpoint := ledgerRows.right.right.left
  have ledgerExact : hsame ledger (append coeff readback) :=
    ledgerRows.right.right.right.right.right.right.left
  have endpointExact : hsame endpoint (append provenance ledger) :=
    ledgerRows.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    ledgerRows.right.right.right.right.right.right.right.right
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary provenanceUnary consumerCont
  exact
    ⟨consumerUnary, consumerCont, endpointExact, ledgerExact, pkgSig⟩

end BEDC.Derived.HypergeometricUp
