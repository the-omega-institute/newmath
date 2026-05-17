import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteSelectorLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source mesh selector locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic source →
        Cont source windows mesh →
          Cont mesh triangle selector →
            Cont selector readback locked →
              PkgSig bundle locked pkg →
                UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                  UnaryHistory source ∧ UnaryHistory mesh ∧ UnaryHistory selector ∧
                    UnaryHistory readback ∧ UnaryHistory locked ∧
                      Cont diagonal dyadic source ∧ Cont source windows mesh ∧
                        Cont mesh triangle selector ∧ Cont selector readback locked ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicSource sourceWindowsMesh meshTriangleSelector
    selectorReadbackLocked lockedPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsMesh
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed meshUnary triangleUnary meshTriangleSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, sourceUnary, meshUnary, selectorUnary,
      readbackUnary, lockedUnary, diagonalDyadicSource, sourceWindowsMesh,
      meshTriangleSelector, selectorReadbackLocked, provenancePkg, lockedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
