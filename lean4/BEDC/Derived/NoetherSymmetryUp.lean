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

end BEDC.Derived.NoetherSymmetryUp
