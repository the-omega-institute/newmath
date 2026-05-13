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
