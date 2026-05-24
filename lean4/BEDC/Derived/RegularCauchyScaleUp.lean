import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyScaleCarrier [AskSetup] [PackageSetup]
    (scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
    UnaryHistory scalarEndpoint ∧ UnaryHistory sourceEndpoint ∧
      UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
        UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory namecert ∧ UnaryHistory endpoint ∧
            Cont scalar window scalarEndpoint ∧ Cont source window sourceEndpoint ∧
              Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                Cont scaledEndpoint budget readback ∧ Cont readback route provenance ∧
                  Cont provenance namecert endpoint ∧ hsame sameRows (append scalar source) ∧
                    PkgSig bundle endpoint pkg

theorem RegularCauchyScaleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint
              scaledEndpoint budget readback sameRows route provenance namecert endpoint bundle
              pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint
              scaledEndpoint budget readback sameRows route provenance namecert endpoint bundle
              pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint
              scaledEndpoint budget readback sameRows route provenance namecert endpoint bundle
              pkg ∧
            hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem RegularCauchyScaleCarrier_source_factorization [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg →
      UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
        UnaryHistory scalarEndpoint ∧ UnaryHistory sourceEndpoint ∧
          UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
            UnaryHistory (append scalar source) ∧ Cont scalar window scalarEndpoint ∧
              Cont source window sourceEndpoint ∧ Cont scalarEndpoint sourceEndpoint
                scaledEndpoint ∧ Cont scaledEndpoint budget readback ∧
                  Cont readback route provenance ∧ Cont provenance namecert endpoint ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier
  have scalarUnary : UnaryHistory scalar := carrier.left
  have sourceUnary : UnaryHistory source := carrier.right.left
  have windowUnary : UnaryHistory window := carrier.right.right.left
  have scalarEndpointUnary : UnaryHistory scalarEndpoint := carrier.right.right.right.left
  have sourceEndpointUnary : UnaryHistory sourceEndpoint :=
    carrier.right.right.right.right.left
  have scaledEndpointUnary : UnaryHistory scaledEndpoint :=
    carrier.right.right.right.right.right.left
  have budgetUnary : UnaryHistory budget := carrier.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    carrier.right.right.right.right.right.right.right.left
  have sameRowsUnary : UnaryHistory sameRows :=
    carrier.right.right.right.right.right.right.right.right.left
  have scalarWindow : Cont scalar window scalarEndpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sourceWindow : Cont source window sourceEndpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointsScaled : Cont scalarEndpoint sourceEndpoint scaledEndpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have scaledBudget : Cont scaledEndpoint budget readback :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have readbackRoute : Cont readback route provenance :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have provenanceNamecert : Cont provenance namecert endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sameRowsAppend : hsame sameRows (append scalar source) :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have appendUnary : UnaryHistory (append scalar source) :=
    unary_transport sameRowsUnary sameRowsAppend
  constructor
  · exact scalarUnary
  · constructor
    · exact sourceUnary
    · constructor
      · exact windowUnary
      · constructor
        · exact scalarEndpointUnary
        · constructor
          · exact sourceEndpointUnary
          · constructor
            · exact scaledEndpointUnary
            · constructor
              · exact budgetUnary
              · constructor
                · exact readbackUnary
                · constructor
                  · exact appendUnary
                  · constructor
                    · exact scalarWindow
                    · constructor
                      · exact sourceWindow
                      · constructor
                        · exact endpointsScaled
                        · constructor
                          · exact scaledBudget
                          · constructor
                            · exact readbackRoute
                            · constructor
                              · exact provenanceNamecert
                              · exact pkgSig

theorem RegularCauchyScaleCarrier_classifier_route_exhaustion [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      hsame routeRead route ->
        UnaryHistory routeRead ∧ UnaryHistory route ∧ Cont readback route provenance ∧
          Cont provenance namecert endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameRouteRead
  obtain ⟨_scalarUnary, _sourceUnary, _windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, _budgetUnary, _readbackUnary,
    _sameRowsUnary, routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary,
    _scalarWindow, _sourceWindow, _endpointsScaled, _scaledBudget, readbackRouteProvenance,
    provenanceNamecertEndpoint, _sameRowsAppend, endpointPkg⟩ := carrier
  exact
    ⟨unary_transport routeUnary (hsame_symm sameRouteRead),
      routeUnary,
      readbackRouteProvenance,
      provenanceNamecertEndpoint,
      endpointPkg⟩

theorem RegularCauchyScaleCarrier_scalar_classifier_stability_obligation
    [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint scalarT sourceT windowT budgetT readbackT : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg →
      hsame scalarT scalar →
        hsame sourceT source →
          hsame windowT window →
            hsame budgetT budget →
              hsame readbackT readback →
                UnaryHistory scalarT ∧ UnaryHistory sourceT ∧ UnaryHistory windowT ∧
                  UnaryHistory budgetT ∧ UnaryHistory readbackT ∧
                    Cont scaledEndpoint budget readback ∧ Cont readback route provenance ∧
                      Cont provenance namecert endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameScalar sameSource sameWindow sameBudget sameReadback
  obtain ⟨scalarUnary, sourceUnary, windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary, _scalarWindow,
    _sourceWindow, _endpointsScaled, scaledBudgetReadback, readbackRouteProvenance,
    provenanceNamecertEndpoint, _sameRowsAppend, endpointPkg⟩ := carrier
  exact
    ⟨unary_transport scalarUnary (hsame_symm sameScalar),
      unary_transport sourceUnary (hsame_symm sameSource),
      unary_transport windowUnary (hsame_symm sameWindow),
      unary_transport budgetUnary (hsame_symm sameBudget),
      unary_transport readbackUnary (hsame_symm sameReadback),
      scaledBudgetReadback,
      readbackRouteProvenance,
      provenanceNamecertEndpoint,
      endpointPkg⟩

theorem RegularCauchyScaleCarrier_real_scalar_non_escape [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint consumer routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg →
      Cont readback route consumer →
        hsame routeRead route →
          PkgSig bundle consumer pkg →
            UnaryHistory readback ∧ UnaryHistory budget ∧ UnaryHistory routeRead ∧
              Cont scaledEndpoint budget readback ∧ Cont readback route consumer ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier readbackRouteConsumer sameRouteRead consumerPkg
  obtain ⟨_scalarUnary, _sourceUnary, _windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, budgetUnary, readbackUnary,
    _sameRowsUnary, routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary,
    _scalarWindow, _sourceWindow, _endpointsScaled, scaledBudgetReadback,
    _readbackRouteProvenance, _provenanceNamecertEndpoint, _sameRowsAppend,
    endpointPkg⟩ := carrier
  exact
    ⟨readbackUnary,
      budgetUnary,
      unary_transport routeUnary (hsame_symm sameRouteRead),
      scaledBudgetReadback,
      readbackRouteConsumer,
      endpointPkg,
      consumerPkg⟩

theorem RegularCauchyScaleCarrier_window_budget [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint precision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      Cont window budget precision ->
        PkgSig bundle precision pkg ->
          UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
            UnaryHistory scalarEndpoint ∧ UnaryHistory sourceEndpoint ∧
              UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory precision ∧
                Cont scalar window scalarEndpoint ∧ Cont source window sourceEndpoint ∧
                  Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                    Cont scaledEndpoint budget readback ∧ Cont window budget precision ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle precision pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowBudget precisionPkg
  obtain ⟨scalarUnary, sourceUnary, windowUnary, scalarEndpointUnary, sourceEndpointUnary,
    scaledEndpointUnary, budgetUnary, _readbackUnary, _sameRowsUnary, _routeUnary,
    _provenanceUnary, _namecertUnary, _endpointUnary, scalarWindow, sourceWindow,
    endpointsScaled, scaledBudget, _readbackRoute, _provenanceNamecert, _sameRowsAppend,
    endpointPkg⟩ := carrier
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed windowUnary budgetUnary windowBudget
  exact
    ⟨scalarUnary,
      sourceUnary,
      windowUnary,
      scalarEndpointUnary,
      sourceEndpointUnary,
      scaledEndpointUnary,
      budgetUnary,
      precisionUnary,
      scalarWindow,
      sourceWindow,
      endpointsScaled,
      scaledBudget,
      windowBudget,
      endpointPkg,
      precisionPkg⟩

theorem RegularCauchyScaleCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scalar ∨ hsame row source ∨ hsame row window ∨
              hsame row scaledEndpoint ∨ hsame row budget ∨ hsame row readback)
          (fun row : BHist => hsame row readback ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
          UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
            Cont scalar window scalarEndpoint ∧ Cont source window sourceEndpoint ∧
              Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                Cont scaledEndpoint budget readback ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨scalarUnary, sourceUnary, windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, scaledEndpointUnary, budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary, scalarWindow,
    sourceWindow, endpointsScaled, scaledBudget, _readbackRoute, _provenanceNamecert,
    _sameRowsAppend, endpointPkg⟩ := carrier
  have sourceReadback : hsame readback readback ∧ UnaryHistory readback :=
    ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scalar ∨ hsame row source ∨ hsame row window ∨
              hsame row scaledEndpoint ∨ hsame row budget ∨ hsame row readback)
          (fun row : BHist => hsame row readback ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceReadback
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows'
        exact hsame_symm sameRows'
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows' sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows') sourceRow.left,
            unary_transport sourceRow.right sameRows'⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, endpointPkg⟩
  }
  exact
    ⟨cert, scalarUnary, sourceUnary, windowUnary, scaledEndpointUnary, budgetUnary,
      readbackUnary, scalarWindow, sourceWindow, endpointsScaled, scaledBudget, endpointPkg⟩

theorem RegularCauchyScaleCarrier_realup_seal_boundary [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      Cont endpoint readback realSeal ->
        PkgSig bundle realSeal pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row readback ∨ hsame row provenance ∨ hsame row endpoint ∨
                  hsame row realSeal)
              (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory readback ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
              UnaryHistory realSeal ∧ Cont readback route provenance ∧
                Cont provenance namecert endpoint ∧ Cont endpoint readback realSeal ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier endpointReadbackSeal realSealPkg
  obtain ⟨_scalarUnary, _sourceUnary, _windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, _budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, provenanceUnary, _namecertUnary, endpointUnary, _scalarWindow,
    _sourceWindow, _endpointsScaled, _scaledBudget, readbackRoute, provenanceNamecert,
    _sameRowsAppend, endpointPkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed endpointUnary readbackUnary endpointReadbackSeal
  have sourceRealSeal : hsame realSeal realSeal ∧ UnaryHistory realSeal :=
    ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row provenance ∨ hsame row endpoint ∨
              hsame row realSeal)
          (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceRealSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows'
        exact hsame_symm sameRows'
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows' sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows') sourceRow.left,
            unary_transport sourceRow.right sameRows'⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, realSealPkg⟩
  }
  exact
    ⟨cert, readbackUnary, provenanceUnary, endpointUnary, realSealUnary, readbackRoute,
      provenanceNamecert, endpointReadbackSeal, endpointPkg, realSealPkg⟩

end BEDC.Derived.RegularCauchyScaleUp
