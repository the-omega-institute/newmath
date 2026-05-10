import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NoetherSymmetryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NoetherSymmetryConservationLedgerCarrier [AskSetup] [PackageSetup]
    (lieSource pdeSource field current lieLedger pdeLedger conservation endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lieSource ∧ UnaryHistory pdeSource ∧ UnaryHistory field ∧
    UnaryHistory current ∧ Cont lieSource field lieLedger ∧
      Cont pdeSource field pdeLedger ∧ Cont lieLedger pdeLedger conservation ∧
        Cont conservation current endpoint ∧ PkgSig bundle endpoint pkg

def NoetherSymmetryCurrentClassifier [AskSetup] [PackageSetup]
    (lieSource pdeSource field current lieLedger pdeLedger conservation endpoint lieSource'
      pdeSource' field' current' lieLedger' pdeLedger' conservation' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
      pdeLedger conservation endpoint bundle pkg ∧
    NoetherSymmetryConservationLedgerCarrier lieSource' pdeSource' field' current'
        lieLedger' pdeLedger' conservation' endpoint' bundle pkg ∧
      hsame lieSource lieSource' ∧ hsame pdeSource pdeSource' ∧ hsame field field' ∧
        hsame current current' ∧ hsame lieLedger lieLedger' ∧
          hsame pdeLedger pdeLedger' ∧ hsame conservation conservation' ∧
            hsame endpoint endpoint'

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

theorem NoetherSymmetryConservationLedgerCarrier_namecert_obligation_surface [AskSetup]
    [PackageSetup]
    {lieSource pdeSource field current lieLedger pdeLedger conservation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
        pdeLedger conservation endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have endpointSource :
      NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
          pdeLedger conservation endpoint bundle pkg ∧ hsame endpoint endpoint :=
    And.intro carrier (hsame_refl endpoint)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          hsame :=
    {
      core := {
        carrier_inhabited := Exists.intro endpoint endpointSource
        equiv_refl := by
          intro h _source
          exact hsame_refl h
        equiv_symm := by
          intro _h _k classified
          exact hsame_symm classified
        equiv_trans := by
          intro _h _k _r classifiedHK classifiedKR
          exact hsame_trans classifiedHK classifiedKR
        carrier_respects_equiv := by
          intro h k sameHK sourceH
          exact And.intro sourceH.left (hsame_trans (hsame_symm sameHK) sourceH.right)
      }
      pattern_sound := by
        intro _h source
        exact source
      ledger_sound := by
        intro _h source
        exact source
    }
  exact And.intro cert carrier.right.right.right.right.right.right.right.right

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

theorem NoetherSymmetryConservationLedgerCarrier_lie_pde_source_boundary
    [AskSetup] [PackageSetup]
    {lieSource pdeSource field current lieLedger pdeLedger conservation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
        pdeLedger conservation endpoint bundle pkg ->
      UnaryHistory lieSource ∧ UnaryHistory pdeSource ∧ UnaryHistory field ∧
        UnaryHistory current ∧ UnaryHistory lieLedger ∧ UnaryHistory pdeLedger ∧
          UnaryHistory conservation ∧ UnaryHistory endpoint ∧
            Cont lieSource field lieLedger ∧ Cont pdeSource field pdeLedger ∧
              Cont lieLedger pdeLedger conservation ∧ Cont conservation current endpoint ∧
                PkgSig bundle endpoint pkg := by
  intro carrier
  have lieLedgerUnary : UnaryHistory lieLedger :=
    unary_cont_closed carrier.left carrier.right.right.left
      carrier.right.right.right.right.left
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
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      lieLedgerUnary,
      pdeLedgerUnary,
      conservationUnary,
      endpointUnary,
        carrier.right.right.right.right.left,
        carrier.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.right.right⟩

theorem NoetherSymmetryConservationLedgerCarrier_finite_current_public_export
    [AskSetup] [PackageSetup]
    {lieSource pdeSource field current lieLedger pdeLedger conservation endpoint exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
        pdeLedger conservation endpoint bundle pkg ->
      Cont endpoint current exportRow ->
        UnaryHistory lieLedger ∧ UnaryHistory pdeLedger ∧ UnaryHistory conservation ∧
          UnaryHistory endpoint ∧ UnaryHistory exportRow ∧
            Cont lieSource field lieLedger ∧ Cont pdeSource field pdeLedger ∧
              Cont lieLedger pdeLedger conservation ∧ Cont conservation current endpoint ∧
                Cont endpoint current exportRow ∧ hsame exportRow (append endpoint current) ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier exportCont
  have lieLedgerUnary : UnaryHistory lieLedger :=
    unary_cont_closed carrier.left carrier.right.right.left
      carrier.right.right.right.right.left
  have pdeLedgerUnary : UnaryHistory pdeLedger :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed lieLedgerUnary pdeLedgerUnary
      carrier.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed conservationUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed endpointUnary carrier.right.right.right.left exportCont
  exact
    ⟨lieLedgerUnary,
      pdeLedgerUnary,
      conservationUnary,
      endpointUnary,
      exportUnary,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      exportCont,
      exportCont,
      carrier.right.right.right.right.right.right.right.right⟩

theorem NoetherSymmetryConservationLedgerCarrier_finite_current_public_boundary
    [AskSetup] [PackageSetup]
    {lieSource pdeSource field current lieLedger pdeLedger conservation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current lieLedger
        pdeLedger conservation endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            NoetherSymmetryConservationLedgerCarrier lieSource pdeSource field current
                lieLedger pdeLedger conservation endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧
        UnaryHistory lieSource ∧ UnaryHistory pdeSource ∧ UnaryHistory field ∧
          UnaryHistory current ∧ UnaryHistory lieLedger ∧ UnaryHistory pdeLedger ∧
            UnaryHistory conservation ∧ UnaryHistory endpoint ∧
              Cont lieSource field lieLedger ∧ Cont pdeSource field pdeLedger ∧
                Cont lieLedger pdeLedger conservation ∧ Cont conservation current endpoint ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier
  have obligation :=
    NoetherSymmetryConservationLedgerCarrier_namecert_obligation_surface carrier
  have boundary :=
    NoetherSymmetryConservationLedgerCarrier_lie_pde_source_boundary carrier
  exact
    ⟨obligation.left,
      boundary.left,
      boundary.right.left,
      boundary.right.right.left,
      boundary.right.right.right.left,
      boundary.right.right.right.right.left,
      boundary.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.right.right.right.right.right.left,
      boundary.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.NoetherSymmetryUp
