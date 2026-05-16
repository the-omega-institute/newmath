import BEDC.Derived.BoundedMonotoneCauchyWitnessUp
import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_diagonal_limit_compatibility_pullback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      diagonal triangle diagSeal dyadic windows readback realSeal diagTransport diagRoute
      diagProvenance diagCert rootPullback terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      BEDC.Derived.DiagonallimitcompatibilityUp.DiagonalLimitCompatibilityCarrier diagonal
          triangle diagSeal dyadic windows readback realSeal diagTransport diagRoute
          diagProvenance diagCert bundle pkg →
        Cont sealRow realSeal rootPullback →
          Cont rootPullback readback terminal →
            PkgSig bundle terminal pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory diagonal ∧ UnaryHistory triangle ∧
                    UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                      UnaryHistory realSeal ∧ UnaryHistory rootPullback ∧
                        UnaryHistory terminal ∧ Cont sealRow realSeal rootPullback ∧
                          Cont rootPullback readback terminal ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle diagProvenance pkg ∧
                                PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro witnessCarrier diagonalCarrier sealRealRoot rootReadTerminal terminalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := witnessCarrier
  obtain ⟨diagonalUnary, triangleUnary, _diagSealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _diagTransportUnary, _diagRouteUnary, _diagProvenanceUnary,
    _diagCertUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, diagProvenancePkg⟩ := diagonalCarrier
  have rootUnary : UnaryHistory rootPullback :=
    unary_cont_closed sealUnary realSealUnary sealRealRoot
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed rootUnary readbackUnary rootReadTerminal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      rootUnary, terminalUnary, sealRealRoot, rootReadTerminal, provenancePkg,
      diagProvenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
