import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NoetherSymmetryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NoetherSymmetryConservationLedgerCarrier [AskSetup] [PackageSetup]
    (lieSource pdeSource field current lieLedger pdeLedger conservation endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lieSource ∧ UnaryHistory pdeSource ∧ UnaryHistory field ∧
    UnaryHistory current ∧ Cont lieSource field lieLedger ∧
      Cont pdeSource field pdeLedger ∧ Cont lieLedger pdeLedger conservation ∧
        Cont conservation current endpoint ∧ PkgSig bundle endpoint pkg

theorem NoetherSymmetryConservationLedgerCarrier_stability [AskSetup] [PackageSetup]
    {lieSource pdeSource field current lieLedger pdeLedger conservation endpoint lieSource'
      pdeSource' field' current' lieLedger' pdeLedger' conservation' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
        pdeLedger conservation endpoint bundle pkg ->
      hsame lieSource lieSource' ->
        hsame pdeSource pdeSource' ->
          hsame field field' ->
            hsame current current' ->
              Cont lieSource' field' lieLedger' ->
                Cont pdeSource' field' pdeLedger' ->
                  Cont lieLedger' pdeLedger' conservation' ->
                    Cont conservation' current' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        NoetherSymmetryConservationLedgerCarrier lieSource' pdeSource' field'
                            current' lieLedger' pdeLedger' conservation' endpoint' bundle pkg ∧
                          hsame endpoint endpoint' := by
  intro carrier sameLieSource samePdeSource sameField sameCurrent lieLedgerCont'
    pdeLedgerCont' conservationCont' endpointCont' endpointPkg'
  have lieLedgerSame : hsame lieLedger lieLedger' :=
    cont_respects_hsame sameLieSource sameField carrier.right.right.right.right.left
      lieLedgerCont'
  have pdeLedgerSame : hsame pdeLedger pdeLedger' :=
    cont_respects_hsame samePdeSource sameField carrier.right.right.right.right.right.left
      pdeLedgerCont'
  have conservationSame : hsame conservation conservation' :=
    cont_respects_hsame lieLedgerSame pdeLedgerSame
      carrier.right.right.right.right.right.right.left conservationCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame conservationSame sameCurrent
      carrier.right.right.right.right.right.right.right.left endpointCont'
  have transportedCarrier :
      NoetherSymmetryConservationLedgerCarrier lieSource' pdeSource' field' current'
        lieLedger' pdeLedger' conservation' endpoint' bundle pkg :=
    And.intro (unary_transport carrier.left sameLieSource)
      (And.intro (unary_transport carrier.right.left samePdeSource)
        (And.intro (unary_transport carrier.right.right.left sameField)
          (And.intro (unary_transport carrier.right.right.right.left sameCurrent)
            (And.intro lieLedgerCont'
              (And.intro pdeLedgerCont'
                (And.intro conservationCont' (And.intro endpointCont' endpointPkg')))))))
  exact And.intro transportedCarrier endpointSame

theorem NoetherSymmetryConservationLedgerCarrier_source_boundary [AskSetup] [PackageSetup]
    {lieSource pdeSource field current lieLedger pdeLedger conservation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
        pdeLedger conservation endpoint bundle pkg ->
      UnaryHistory lieLedger ∧ UnaryHistory pdeLedger ∧ UnaryHistory conservation ∧
        UnaryHistory endpoint ∧ hsame lieLedger (append lieSource field) ∧
          hsame pdeLedger (append pdeSource field) ∧
            hsame conservation (append lieLedger pdeLedger) ∧
              hsame endpoint (append conservation current) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have lieLedgerUnary : UnaryHistory lieLedger :=
    unary_cont_closed carrier.left carrier.right.right.left carrier.right.right.right.right.left
  have pdeLedgerUnary : UnaryHistory pdeLedger :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed lieLedgerUnary pdeLedgerUnary
      carrier.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed conservationUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  exact
    And.intro lieLedgerUnary
      (And.intro pdeLedgerUnary
        (And.intro conservationUnary
          (And.intro endpointUnary
            (And.intro carrier.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    carrier.right.right.right.right.right.right.right.right)))))))

end BEDC.Derived.NoetherSymmetryUp
