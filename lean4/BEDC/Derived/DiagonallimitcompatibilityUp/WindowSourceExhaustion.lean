import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_window_source_exhaustion [AskSetup] [PackageSetup]
    {source triangle sealRoute tolerance window readback realSeal transport route provenance
      localCert sourceRead windowRead toleranceRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier source triangle sealRoute tolerance window readback realSeal
        transport route provenance localCert bundle pkg →
      Cont source window sourceRead →
        Cont sourceRead tolerance windowRead →
          Cont windowRead readback toleranceRead →
            Cont toleranceRead realSeal terminalRead →
              PkgSig bundle terminalRead pkg →
                UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory tolerance ∧
                  UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory sourceRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory terminalRead ∧ Cont source window sourceRead ∧
                        Cont sourceRead tolerance windowRead ∧
                          Cont windowRead readback toleranceRead ∧
                            Cont toleranceRead realSeal terminalRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceWindow sourceReadTolerance windowReadReadback toleranceReadRealSeal
    terminalPkg
  obtain ⟨sourceUnary, _triangleUnary, _sealRouteUnary, toleranceUnary, windowUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _sourceTriangleSealRoute, _toleranceWindowReadback,
    _readbackRealSealRoute, _routeLocalCertTransport, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceReadUnary toleranceUnary sourceReadTolerance
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowReadUnary readbackUnary windowReadReadback
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed toleranceReadUnary realSealUnary toleranceReadRealSeal
  exact
    ⟨sourceUnary, windowUnary, toleranceUnary, readbackUnary, realSealUnary, sourceReadUnary,
      windowReadUnary, toleranceReadUnary, terminalReadUnary, sourceWindow, sourceReadTolerance,
      windowReadReadback, toleranceReadRealSeal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
