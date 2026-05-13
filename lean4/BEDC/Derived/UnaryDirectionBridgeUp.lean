import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnaryDirectionBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UnaryDirectionBridgeCarrier [AskSetup] [PackageSetup]
    (natRow axisRow bridge kernel boundary ledger transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory natRow ∧ UnaryHistory axisRow ∧ UnaryHistory bridge ∧
    UnaryHistory kernel ∧ UnaryHistory boundary ∧ UnaryHistory ledger ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
          Cont boundary ledger transports ∧ Cont transports routes provenance ∧
            Cont routes provenance name ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem UnaryDirectionBridgeCarrier_kernel_distinct_obligations [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      UnaryHistory natRow ∧ UnaryHistory axisRow ∧ UnaryHistory bridge ∧
        UnaryHistory kernel ∧ UnaryHistory boundary ∧
          Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
              SemanticNameCert
                (fun row : BHist =>
                  UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger
                      transports routes provenance name bundle pkg ∧
                    hsame row name)
                (fun row : BHist =>
                  UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger
                      transports routes provenance name bundle pkg ∧
                    hsame row name)
                (fun row : BHist =>
                  UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger
                      transports routes provenance name bundle pkg ∧
                    hsame row name)
                hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness :
      UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg := carrier
  obtain ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, _ledgerUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have nameCert :
      SemanticNameCert
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro name (And.intro carrierWitness (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, natAxisBridge,
      bridgeKernelBoundary, provenancePkg, namePkg, nameCert⟩

theorem UnaryDirectionBridgeCarrier_standard_boundary_readout [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      boundaryRead additiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont boundary ledger boundaryRead ->
        Cont boundaryRead routes additiveRead ->
          PkgSig bundle boundaryRead pkg ->
            PkgSig bundle additiveRead pkg ->
              UnaryHistory boundaryRead ∧ UnaryHistory additiveRead ∧
                Cont bridge kernel boundary ∧ Cont boundary ledger transports ∧
                  Cont boundary ledger boundaryRead ∧ Cont boundaryRead routes additiveRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
                      PkgSig bundle additiveRead pkg := by
  intro carrier boundaryLedgerRead readRoutesAdditive boundaryReadPkg additiveReadPkg
  obtain ⟨_natUnary, _axisUnary, _bridgeUnary, _kernelUnary, boundaryUnary, ledgerUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _natAxisBridge,
    bridgeKernelBoundary, boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary ledgerUnary boundaryLedgerRead
  have additiveReadUnary : UnaryHistory additiveRead :=
    unary_cont_closed boundaryReadUnary routesUnary readRoutesAdditive
  exact
    ⟨boundaryReadUnary, additiveReadUnary, bridgeKernelBoundary, boundaryLedgerTransports,
      boundaryLedgerRead, readRoutesAdditive, provenancePkg, boundaryReadPkg, additiveReadPkg⟩

theorem UnaryDirectionBridgeCarrier_source_classifier_transport [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      natRow' axisRow' bridge' kernel' boundary' ledger' transports' routes'
      provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      hsame natRow natRow' ->
        hsame axisRow axisRow' ->
          hsame bridge bridge' ->
            hsame kernel kernel' ->
              hsame boundary boundary' ->
                hsame ledger ledger' ->
                  hsame transports transports' ->
                    hsame routes routes' ->
                      hsame provenance provenance' ->
                        hsame name name' ->
                          UnaryDirectionBridgeCarrier natRow' axisRow' bridge' kernel'
                            boundary' ledger' transports' routes' provenance' name'
                            bundle pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  intro carrier sameNat sameAxis sameBridge sameKernel sameBoundary sameLedger
    sameTransports sameRoutes sameProvenance sameName
  cases sameNat
  cases sameAxis
  cases sameBridge
  cases sameKernel
  cases sameBoundary
  cases sameLedger
  cases sameTransports
  cases sameRoutes
  cases sameProvenance
  cases sameName
  exact carrier

end BEDC.Derived.UnaryDirectionBridgeUp
