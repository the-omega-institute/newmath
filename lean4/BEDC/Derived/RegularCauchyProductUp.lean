import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

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

end BEDC.Derived.RegularCauchyProductUp
