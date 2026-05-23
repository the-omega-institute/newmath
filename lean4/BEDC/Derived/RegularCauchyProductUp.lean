import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.RegularCauchyDifferenceUp
import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyProductCarrier [AskSetup] [PackageSetup]
    (sourceA sourceB windowA windowB endpointA endpointB product budget readback
      transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
    UnaryHistory windowB ∧ UnaryHistory endpointA ∧ UnaryHistory endpointB ∧
      UnaryHistory budget ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        Cont windowA windowB transport ∧ Cont endpointA endpointB product ∧
          Cont product budget readback ∧ Cont provenance transport name ∧ PkgSig bundle name pkg

theorem RegularCauchyProductCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback
      transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB
        product budget readback transport route provenance name bundle pkg ->
      UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
        UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory budget ∧
          UnaryHistory readback ∧ Cont windowA windowB transport ∧
            Cont endpointA endpointB product ∧ Cont product budget readback ∧
              hsame name (append provenance transport) ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, _provenanceUnary, windowTransportRow,
    endpointProductRow, productBudgetRow, provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary, budgetUnary,
      readbackUnary, windowTransportRow, endpointProductRow, productBudgetRow,
      provenanceTransportName, namePkg⟩

theorem RegularCauchyProductCarrier_window_budget [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      UnaryHistory windowA /\ UnaryHistory windowB /\ UnaryHistory endpointA /\
        UnaryHistory endpointB /\ UnaryHistory product /\ UnaryHistory budget /\
          Cont windowA windowB transport /\ Cont endpointA endpointB product /\
            Cont product budget readback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, _provenanceUnary, windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, _namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  exact
    ⟨windowAUnary, windowBUnary, endpointAUnary, endpointBUnary, productUnary, budgetUnary,
      windowTransportRow, endpointProductRow, productBudgetRow⟩

theorem RegularCauchyProductCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name readbackConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback provenance readbackConsumer ->
        PkgSig bundle readbackConsumer pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory product ∧
            UnaryHistory budget ∧ UnaryHistory readback ∧ UnaryHistory readbackConsumer ∧
              Cont endpointA endpointB product ∧ Cont product budget readback ∧
                Cont readback provenance readbackConsumer ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle readbackConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier readbackProvenanceConsumer readbackConsumerPkg
  obtain ⟨sourceAUnary, sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have readbackConsumerUnary : UnaryHistory readbackConsumer :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceConsumer
  exact
    ⟨sourceAUnary, sourceBUnary, productUnary, budgetUnary, readbackUnary,
      readbackConsumerUnary, endpointProductRow, productBudgetRow, readbackProvenanceConsumer,
      namePkg, readbackConsumerPkg⟩

theorem RegularCauchyProductCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback provenance realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory budget ∧
              UnaryHistory readback ∧ UnaryHistory realRead ∧
                Cont endpointA endpointB product ∧ Cont product budget readback ∧
                  Cont readback provenance realRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier readbackProvenanceRead realReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceRead
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary, budgetUnary,
      readbackUnary, realReadUnary, endpointProductRow, productBudgetRow,
      readbackProvenanceRead, namePkg, realReadPkg⟩

theorem RegularCauchyProductCarrier_bounded_source_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback budget boundedRead ->
        PkgSig bundle boundedRead pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory budget ∧
              UnaryHistory readback ∧ UnaryHistory boundedRead ∧
                Cont endpointA endpointB product ∧ Cont product budget readback ∧
                  Cont readback budget boundedRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle boundedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackBudgetBounded boundedReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, _provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed readbackUnary budgetUnary readbackBudgetBounded
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary, budgetUnary,
      readbackUnary, boundedReadUnary, endpointProductRow, productBudgetRow,
      readbackBudgetBounded, namePkg, boundedReadPkg⟩

theorem RegularCauchyProductCarrier_error_budget_exactness [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback budget budgetRead ->
        PkgSig bundle budgetRead pkg ->
          UnaryHistory endpointA ∧ UnaryHistory endpointB ∧ UnaryHistory product ∧
            UnaryHistory budget ∧ UnaryHistory readback ∧ UnaryHistory budgetRead ∧
              Cont endpointA endpointB product ∧ Cont product budget readback ∧
                Cont readback budget budgetRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackBudget budgetReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, _provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed readbackUnary budgetUnary readbackBudget
  exact
    ⟨endpointAUnary, endpointBUnary, productUnary, budgetUnary, readbackUnary,
      budgetReadUnary, endpointProductRow, productBudgetRow, readbackBudget, namePkg,
      budgetReadPkg⟩

theorem RegularCauchyProductCarrier_source_window_transport [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name sourceA' sourceB' windowA' windowB' transport' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      hsame sourceA sourceA' ->
        hsame sourceB sourceB' ->
          hsame windowA windowA' ->
            hsame windowB windowB' ->
              Cont windowA' windowB' transport' ->
                hsame transport transport' /\ UnaryHistory sourceA' /\ UnaryHistory sourceB' /\
                  UnaryHistory windowA' /\ UnaryHistory windowB' /\ Cont windowA windowB transport /\
                    Cont windowA' windowB' transport' := by
  intro carrier sourceASame sourceBSame windowASame windowBSame transportedWindow
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _endpointAUnary,
    _endpointBUnary, _budgetUnary, _routeUnary, _provenanceUnary, windowTransportRow,
    _endpointProductRow, _productBudgetRow, _provenanceTransportName, _namePkg⟩ := carrier
  have sourceAUnary' : UnaryHistory sourceA' :=
    unary_transport sourceAUnary sourceASame
  have sourceBUnary' : UnaryHistory sourceB' :=
    unary_transport sourceBUnary sourceBSame
  have windowAUnary' : UnaryHistory windowA' :=
    unary_transport windowAUnary windowASame
  have windowBUnary' : UnaryHistory windowB' :=
    unary_transport windowBUnary windowBSame
  have transportSame : hsame transport transport' :=
    cont_respects_hsame windowASame windowBSame windowTransportRow transportedWindow
  exact
    ⟨transportSame, sourceAUnary', sourceBUnary', windowAUnary', windowBUnary',
      windowTransportRow, transportedWindow⟩

theorem RegularCauchyProductCarrier_window_comparison [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport
      route provenance name sumEndpoint sumBudget sumReadback sumTransports sumRoutes
      sumProvenance sumLocalCert diffSchedule diffTolerance diffNullConsumer diffTransport
      diffRoute diffProvenance diffLocalCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB
        product budget readback transport route provenance name bundle pkg ->
      BEDC.Derived.RegularCauchySumUp.RegularCauchySumCarrier sourceA sourceB windowA
        windowB endpointA endpointB sumEndpoint sumBudget sumReadback sumTransports
        sumRoutes sumProvenance sumLocalCert bundle pkg ->
        BEDC.Derived.RegularCauchyDifferenceUp.RegularCauchyDifferenceCarrier sourceA
          sourceB diffSchedule diffTolerance diffNullConsumer diffTransport diffRoute
          diffProvenance diffLocalCert bundle pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ Cont windowA windowB transport ∧
              Cont endpointA endpointB product ∧ Cont endpointA endpointB sumEndpoint ∧
                Cont sourceA sourceB diffSchedule ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle sumProvenance pkg ∧ PkgSig bundle diffProvenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro productCarrier sumCarrier diffCarrier
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _endpointAUnary,
    _endpointBUnary, _budgetUnary, _routeUnary, _provenanceUnary, windowTransportRow,
    endpointProductRow, _productBudgetRow, _provenanceTransportName, namePkg⟩ :=
    productCarrier
  obtain ⟨_sumSourceAUnary, _sumSourceBUnary, _sumWindowAUnary, _sumWindowBUnary,
    _sumEndpointAUnary, _sumEndpointBUnary, _sumBudgetUnary, _sumTransportsUnary,
    _sumRoutesUnary, _sumProvenanceUnary, _sumLocalCertUnary, _sumLeftRoute,
    _sumRightRoute, sumEndpointRow, _sumReadbackRow, _sumProvenanceRow,
    sumProvenancePkg⟩ := sumCarrier
  obtain ⟨_diffSourceAUnary, _diffSourceBUnary, _diffScheduleUnary,
    _diffToleranceUnary, _diffNullConsumerUnary, _diffTransportUnary, _diffRouteUnary,
    _diffProvenanceUnary, _diffLocalCertUnary, diffScheduleRow, _diffNullConsumerRow,
    _diffRouteRow, _diffProvenanceRow, diffProvenancePkg, _diffNameCert⟩ :=
    diffCarrier
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, windowTransportRow,
      endpointProductRow, sumEndpointRow, diffScheduleRow, namePkg, sumProvenancePkg,
      diffProvenancePkg⟩

theorem RegularCauchyProductCarrier_classifier_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name sourceA' sourceB' endpointA' endpointB' product' budget' readback'
      stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product
        budget readback transport route provenance name bundle pkg ->
      hsame sourceA sourceA' ->
        hsame sourceB sourceB' ->
          hsame endpointA endpointA' ->
            hsame endpointB endpointB' ->
              hsame budget budget' ->
                Cont endpointA' endpointB' product' ->
                  Cont product' budget' readback' ->
                    Cont readback' provenance stableRead ->
                      PkgSig bundle stableRead pkg ->
                        UnaryHistory sourceA' ∧ UnaryHistory sourceB' ∧
                          UnaryHistory endpointA' ∧ UnaryHistory endpointB' ∧
                            UnaryHistory product' ∧ UnaryHistory budget' ∧
                              UnaryHistory readback' ∧ UnaryHistory stableRead ∧
                                hsame product product' ∧ hsame readback readback' ∧
                                  Cont endpointA' endpointB' product' ∧
                                    Cont product' budget' readback' ∧
                                      Cont readback' provenance stableRead ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle stableRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier sameSourceA sameSourceB sameEndpointA sameEndpointB sameBudget
    transportedProduct transportedReadback stableReadRow stableReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have sourceAUnary' : UnaryHistory sourceA' :=
    unary_transport sourceAUnary sameSourceA
  have sourceBUnary' : UnaryHistory sourceB' :=
    unary_transport sourceBUnary sameSourceB
  have endpointAUnary' : UnaryHistory endpointA' :=
    unary_transport endpointAUnary sameEndpointA
  have endpointBUnary' : UnaryHistory endpointB' :=
    unary_transport endpointBUnary sameEndpointB
  have budgetUnary' : UnaryHistory budget' :=
    unary_transport budgetUnary sameBudget
  have productUnary' : UnaryHistory product' :=
    unary_cont_closed endpointAUnary' endpointBUnary' transportedProduct
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed productUnary' budgetUnary' transportedReadback
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed readbackUnary' provenanceUnary stableReadRow
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameEndpointA sameEndpointB endpointProductRow transportedProduct
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameProduct sameBudget productBudgetRow transportedReadback
  exact
    ⟨sourceAUnary', sourceBUnary', endpointAUnary', endpointBUnary', productUnary',
      budgetUnary', readbackUnary', stableReadUnary, sameProduct, sameReadback,
      transportedProduct, transportedReadback, stableReadRow, namePkg, stableReadPkg⟩

theorem RegularCauchyProductCarrier_downstream_source_lock [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback
      transport route provenance name regConsumer realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB
        product budget readback transport route provenance name bundle pkg ->
      Cont readback provenance regConsumer ->
        Cont regConsumer route realConsumer ->
          PkgSig bundle realConsumer pkg ->
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
              UnaryHistory windowB ∧ UnaryHistory readback ∧ UnaryHistory regConsumer ∧
                UnaryHistory realConsumer ∧ Cont windowA windowB transport ∧
                  Cont endpointA endpointB product ∧ Cont product budget readback ∧
                    Cont readback provenance regConsumer ∧
                      Cont regConsumer route realConsumer ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackProvenanceConsumer consumerRouteReal realConsumerPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, routeUnary, provenanceUnary, windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have regConsumerUnary : UnaryHistory regConsumer :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceConsumer
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed regConsumerUnary routeUnary consumerRouteReal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, readbackUnary,
      regConsumerUnary, realConsumerUnary, windowTransportRow, endpointProductRow,
      productBudgetRow, readbackProvenanceConsumer, consumerRouteReal, namePkg,
      realConsumerPkg⟩

theorem RegularCauchyProductCarrier_real_algebra_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name algebraRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback provenance algebraRead ->
        PkgSig bundle algebraRead pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory endpointA ∧ UnaryHistory endpointB ∧
              UnaryHistory product ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
                UnaryHistory algebraRead ∧ Cont windowA windowB transport ∧
                  Cont endpointA endpointB product ∧ Cont product budget readback ∧
                    Cont readback provenance algebraRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle algebraRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackProvenanceAlgebra algebraReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, provenanceUnary, windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have algebraReadUnary : UnaryHistory algebraRead :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceAlgebra
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, endpointAUnary,
      endpointBUnary, productUnary, budgetUnary, readbackUnary, algebraReadUnary,
      windowTransportRow, endpointProductRow, productBudgetRow, readbackProvenanceAlgebra,
      namePkg, algebraReadPkg⟩

theorem RegularCauchyProductCarrier_real_seal_product_budget [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name budgetRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback budget budgetRead ->
        Cont budgetRead route realSeal ->
          PkgSig bundle realSeal pkg ->
            UnaryHistory budgetRead ∧ UnaryHistory realSeal ∧
              Cont readback budget budgetRead ∧ Cont budgetRead route realSeal ∧
                PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackBudgetRead budgetRouteSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, routeUnary, _provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed readbackUnary budgetUnary readbackBudgetRead
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetReadUnary routeUnary budgetRouteSeal
  exact
    ⟨budgetReadUnary, realSealUnary, readbackBudgetRead, budgetRouteSeal, namePkg,
      realSealPkg⟩

theorem RegularCauchyProductCarrier_coordinate_regularity [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name coordinateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback product coordinateRead ->
        PkgSig bundle coordinateRead pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory endpointA ∧
            UnaryHistory endpointB ∧ UnaryHistory product ∧ UnaryHistory budget ∧
              UnaryHistory readback ∧ UnaryHistory coordinateRead ∧
                Cont endpointA endpointB product ∧ Cont product budget readback ∧
                  Cont readback product coordinateRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle coordinateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier coordinateRoute coordinatePkg
  obtain ⟨sourceAUnary, sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, _provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have coordinateUnary : UnaryHistory coordinateRead :=
    unary_cont_closed readbackUnary productUnary coordinateRoute
  exact
    ⟨sourceAUnary, sourceBUnary, endpointAUnary, endpointBUnary, productUnary,
      budgetUnary, readbackUnary, coordinateUnary, endpointProductRow, productBudgetRow,
      coordinateRoute, namePkg, coordinatePkg⟩

theorem RegularCauchyProductCarrier_public_export_certificate [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name regConsumer realConsumer publicExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product budget
        readback transport route provenance name bundle pkg ->
      Cont readback provenance regConsumer ->
        Cont regConsumer route realConsumer ->
          Cont realConsumer budget publicExport ->
            PkgSig bundle publicExport pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory product ∧
                UnaryHistory readback ∧ UnaryHistory regConsumer ∧ UnaryHistory realConsumer ∧
                  UnaryHistory publicExport ∧ Cont readback provenance regConsumer ∧
                    Cont regConsumer route realConsumer ∧ Cont realConsumer budget publicExport ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle publicExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier readbackProvenanceConsumer consumerRouteReal realBudgetExport publicExportPkg
  obtain ⟨sourceAUnary, sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, routeUnary, provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have regConsumerUnary : UnaryHistory regConsumer :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceConsumer
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed regConsumerUnary routeUnary consumerRouteReal
  have publicExportUnary : UnaryHistory publicExport :=
    unary_cont_closed realConsumerUnary budgetUnary realBudgetExport
  exact
    ⟨sourceAUnary, sourceBUnary, productUnary, readbackUnary, regConsumerUnary,
      realConsumerUnary, publicExportUnary, readbackProvenanceConsumer, consumerRouteReal,
      realBudgetExport, namePkg, publicExportPkg⟩

theorem RegularCauchyProductCarrier_real_pair_seal [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB endpointA endpointB product budget readback transport route
      provenance name pairRead realPairSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductCarrier sourceA sourceB windowA windowB endpointA endpointB product
        budget readback transport route provenance name bundle pkg ->
      Cont sourceA sourceB pairRead ->
        Cont readback provenance realPairSeal ->
          PkgSig bundle realPairSeal pkg ->
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory pairRead ∧
              UnaryHistory product ∧ UnaryHistory readback ∧ UnaryHistory realPairSeal ∧
                Cont sourceA sourceB pairRead ∧ Cont endpointA endpointB product ∧
                  Cont product budget readback ∧ Cont readback provenance realPairSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle realPairSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourcePairRead readbackProvenanceSeal realPairSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, _windowAUnary, _windowBUnary, endpointAUnary,
    endpointBUnary, budgetUnary, _routeUnary, provenanceUnary, _windowTransportRow,
    endpointProductRow, productBudgetRow, _provenanceTransportName, namePkg⟩ := carrier
  have pairReadUnary : UnaryHistory pairRead :=
    unary_cont_closed sourceAUnary sourceBUnary sourcePairRead
  have productUnary : UnaryHistory product :=
    unary_cont_closed endpointAUnary endpointBUnary endpointProductRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary budgetUnary productBudgetRow
  have realPairSealUnary : UnaryHistory realPairSeal :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceSeal
  exact
    ⟨sourceAUnary, sourceBUnary, pairReadUnary, productUnary, readbackUnary,
      realPairSealUnary, sourcePairRead, endpointProductRow, productBudgetRow,
      readbackProvenanceSeal, namePkg, realPairSealPkg⟩

end BEDC.Derived.RegularCauchyProductUp
