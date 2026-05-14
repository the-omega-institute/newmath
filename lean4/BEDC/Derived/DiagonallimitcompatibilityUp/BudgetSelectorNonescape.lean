import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityBudgetSelectorNonescape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selectedWindow selectedRead selectedSeal finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selector ->
        Cont selector windows selectedWindow ->
          Cont selectedWindow readback selectedRead ->
            Cont selectedRead realSeal selectedSeal ->
              Cont selectedSeal cert finalRead ->
                PkgSig bundle selectedSeal pkg ->
                  PkgSig bundle finalRead pkg ->
                    UnaryHistory selector ∧ UnaryHistory selectedWindow ∧
                      UnaryHistory selectedRead ∧ UnaryHistory selectedSeal ∧
                        UnaryHistory finalRead ∧ Cont diagonal dyadic selector ∧
                          Cont selector windows selectedWindow ∧
                            Cont selectedWindow readback selectedRead ∧
                              Cont selectedRead realSeal selectedSeal ∧
                                Cont selectedSeal cert finalRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle selectedSeal pkg ∧
                                      PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicSelector selectorWindowsSelectedWindow
    selectedWindowReadbackSelectedRead selectedReadRealSealSelectedSeal
    selectedSealCertFinalRead selectedSealPkg finalReadPkg
  have selected :=
    DiagonalLimitCompatibilityBudgetSelectorCarrier carrier diagonalDyadicSelector
      selectorWindowsSelectedWindow selectedWindowReadbackSelectedRead
      selectedReadRealSealSelectedSeal selectedSealPkg
  obtain ⟨_diagonalUnary, _dyadicUnary, _windowsUnary, _readbackUnary, _realSealUnary,
    selectorUnary, selectedWindowUnary, selectedReadUnary, selectedSealUnary,
    _diagonalDyadicSelector, _selectorWindowsSelectedWindow,
    _selectedWindowReadbackSelectedRead, _selectedReadRealSealSelectedSeal,
    provenancePkg, _selectedSealPkg⟩ := selected
  obtain ⟨_diagonalUnaryCarrier, _triangleUnary, _sealUnary, _dyadicUnaryCarrier,
    _windowsUnaryCarrier, _readbackUnaryCarrier, _realSealUnaryCarrier,
    _transportUnary, _routeUnary, _provenanceUnary, certUnary, _diagonalTriangleSeal,
    _dyadicWindowsReadback, _readbackRealSealRoute, _routeCertTransport,
    _provenancePkgCarrier⟩ := carrier
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed selectedSealUnary certUnary selectedSealCertFinalRead
  exact
    ⟨selectorUnary, selectedWindowUnary, selectedReadUnary, selectedSealUnary,
      finalReadUnary, diagonalDyadicSelector, selectorWindowsSelectedWindow,
      selectedWindowReadbackSelectedRead, selectedReadRealSealSelectedSeal,
      selectedSealCertFinalRead, provenancePkg, selectedSealPkg, finalReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
