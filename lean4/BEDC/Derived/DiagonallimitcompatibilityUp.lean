import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalLimitCompatibilityCarrier [AskSetup] [PackageSetup]
    (diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧ UnaryHistory dyadic ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
          Cont readback realSeal route ∧ Cont route cert transport ∧
            PkgSig bundle provenance pkg

theorem DiagonalLimitCompatibilityNonEscape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackEndpoint endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, endpointUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackEndpoint, provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibilityCarrier_selector_budget_source_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          PkgSig bundle locked pkg ->
            UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory selector ∧ UnaryHistory locked ∧ Cont diagonal windows selector ∧
                Cont selector readback locked ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, selectorUnary, lockedUnary,
      diagonalWindowsSelector, selectorReadbackLocked, provenancePkg, lockedPkg⟩

theorem DiagonalLimitCompatibilityBudgetSourceLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source mesh locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic source ->
        Cont source windows mesh ->
          Cont mesh triangle locked ->
            PkgSig bundle locked pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory source ∧ UnaryHistory mesh ∧ UnaryHistory locked ∧
                  Cont diagonal dyadic source ∧ Cont source windows mesh ∧
                    Cont mesh triangle locked ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicSource sourceWindowsMesh meshTriangleLocked lockedPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsMesh
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed meshUnary triangleUnary meshTriangleLocked
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, sourceUnary, meshUnary, lockedUnary,
      diagonalDyadicSource, sourceWindowsMesh, meshTriangleLocked, provenancePkg, lockedPkg⟩

theorem DiagonalLimitCompatibilitySealBudgetRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          PkgSig bundle sealBudget pkg ->
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
              UnaryHistory sealRow ∧ UnaryHistory sealBudget ∧
                Cont dyadic windows budgetPrefix ∧ Cont budgetPrefix sealRow sealBudget ∧
                  Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealBudget pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow sealBudgetPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSealRow
  exact
    ⟨dyadicUnary, windowsUnary, budgetPrefixUnary, sealUnary, sealBudgetUnary,
      dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackRealSealRoute, provenancePkg,
      sealBudgetPkg⟩

theorem DiagonalLimitCompatibility_tolerance_ledger_handoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows readback ->
        Cont readback realSeal endpoint ->
          UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
            UnaryHistory endpoint ∧ Cont dyadic windows readback ∧
              Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier dyadicWindowsReadback readbackEndpoint
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _carrierDyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, endpointUnary, dyadicWindowsReadback,
      readbackEndpoint, provenancePkg⟩

theorem DiagonalLimitCompatibility_seal_consumer_factorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
            UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
              UnaryHistory endpoint ∧ Cont diagonal triangle sealRow ∧
                Cont dyadic windows readback ∧ Cont readback realSeal endpoint ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackEndpoint endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      endpointUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackEndpoint,
      provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibility_window_route_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory selector ∧ UnaryHistory locked ∧ UnaryHistory endpoint ∧
                  Cont diagonal windows selector ∧ Cont selector readback locked ∧
                    Cont locked realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, selectorUnary, lockedUnary,
      endpointUnary, diagonalWindowsSelector, selectorReadbackLocked,
      lockedRealSealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
