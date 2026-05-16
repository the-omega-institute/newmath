import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_tail_selector_scope [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorRead windowRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle selectorRead ->
        Cont selectorRead windows windowRead ->
          Cont windowRead readback consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory selectorRead ∧ UnaryHistory windowRead ∧ UnaryHistory consumer ∧
                Cont diagonal triangle selectorRead ∧ Cont selectorRead windows windowRead ∧
                  Cont windowRead readback consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalTriangleSelector selectorWindowsRead windowReadbackConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleSelector
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed selectorReadUnary windowsUnary selectorWindowsRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowReadUnary readbackUnary windowReadbackConsumer
  exact
    ⟨selectorReadUnary, windowReadUnary, consumerUnary, diagonalTriangleSelector,
      selectorWindowsRead, windowReadbackConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
