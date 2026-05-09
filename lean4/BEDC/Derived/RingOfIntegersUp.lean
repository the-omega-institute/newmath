import BEDC.Derived.IntUp
import BEDC.Derived.NumFieldUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.Derived.IntUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.NumFieldUp

def RingOfIntegersDedekindSourceCarrier [AskSetup] [PackageSetup]
    (numfield embeddedInt embedding equationLedger classifier provenance contLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  NumFieldRatReflexiveCarrier numfield ∧ UnaryHistory embeddedInt ∧ UnaryHistory embedding ∧
    UnaryHistory equationLedger ∧ UnaryHistory classifier ∧ UnaryHistory provenance ∧
      Cont numfield embeddedInt embedding ∧ Cont embedding equationLedger contLedger ∧
        Cont provenance contLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem RingOfIntegersDedekindSourceCarrier_dependency_projection_boundary [AskSetup]
    [PackageSetup]
    {numfield embeddedInt embedding equationLedger classifier provenance contLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersDedekindSourceCarrier numfield embeddedInt embedding equationLedger
      classifier provenance contLedger endpoint bundle pkg ->
      NumFieldRatReflexiveCarrier numfield ∧ UnaryHistory embeddedInt ∧
        UnaryHistory embedding ∧ UnaryHistory equationLedger ∧ UnaryHistory classifier ∧
          UnaryHistory contLedger ∧ UnaryHistory endpoint ∧ Cont numfield embeddedInt embedding ∧
            Cont embedding equationLedger contLedger ∧ Cont provenance contLedger endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  have contLedgerUnary : UnaryHistory contLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left contLedgerUnary
      carrier.right.right.right.right.right.right.right.right.left
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro contLedgerUnary
              (And.intro endpointUnary
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    (And.intro carrier.right.right.right.right.right.right.right.right.left
                      carrier.right.right.right.right.right.right.right.right.right)))))))))

def RingOfIntegersEquationLedgerCarrier [AskSetup] [PackageSetup]
    (numfield introw embedding ledger classifier controw pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory numfield ∧ UnaryHistory introw ∧ UnaryHistory embedding ∧
    UnaryHistory ledger ∧ UnaryHistory classifier ∧ Cont embedding ledger controw ∧
      Cont controw classifier pkgrow ∧ PkgSig bundle pkgrow pkg

theorem RingOfIntegersEquationLedgerCarrier_finite_ledger_readback [AskSetup] [PackageSetup]
    {numfield introw embedding ledger classifier controw pkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersEquationLedgerCarrier numfield introw embedding ledger classifier controw
        pkgrow bundle pkg ->
      UnaryHistory controw ∧ UnaryHistory pkgrow ∧ hsame controw (append embedding ledger) ∧
        hsame pkgrow (append controw classifier) ∧ PkgSig bundle pkgrow pkg := by
  intro carrier
  cases carrier with
  | intro _numfieldUnary rest =>
      cases rest with
      | intro _introwUnary rest =>
          cases rest with
          | intro embeddingUnary rest =>
              cases rest with
              | intro ledgerUnary rest =>
                  cases rest with
                  | intro classifierUnary rest =>
                      cases rest with
                      | intro contLedger rest =>
                          cases rest with
                          | intro pkgLedger pkgSig =>
                              have controwUnary : UnaryHistory controw :=
                                unary_cont_closed embeddingUnary ledgerUnary contLedger
                              have pkgrowUnary : UnaryHistory pkgrow :=
                                unary_cont_closed controwUnary classifierUnary pkgLedger
                              exact And.intro controwUnary
                                (And.intro pkgrowUnary
                                  (And.intro contLedger
                                    (And.intro pkgLedger pkgSig)))

theorem RingOfIntegersDedekindSourceCarrier_equation_ledger_transport_closure
    [AskSetup] [PackageSetup]
    {numfield introw embedding ledger classifier controw pkgrow ledger' classifier' controw'
      pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersEquationLedgerCarrier numfield introw embedding ledger classifier controw
        pkgrow bundle pkg ->
      hsame ledger ledger' ->
        hsame classifier classifier' ->
          Cont embedding ledger' controw' ->
            Cont controw' classifier' pkgrow' ->
              PkgSig bundle pkgrow' pkg ->
                RingOfIntegersEquationLedgerCarrier numfield introw embedding ledger'
                    classifier' controw' pkgrow' bundle pkg ∧
                  hsame controw controw' ∧ hsame pkgrow pkgrow' := by
  intro carrier sameLedger sameClassifier targetLedgerCont targetPkgCont targetPkgSig
  cases carrier with
  | intro numfieldUnary rest =>
      cases rest with
      | intro introwUnary rest =>
          cases rest with
          | intro embeddingUnary rest =>
              cases rest with
              | intro ledgerUnary rest =>
                  cases rest with
                  | intro classifierUnary rest =>
                      cases rest with
                      | intro ledgerCont rest =>
                          cases rest with
                          | intro pkgCont _ =>
                              have ledgerUnary' : UnaryHistory ledger' :=
                                unary_transport ledgerUnary sameLedger
                              have classifierUnary' : UnaryHistory classifier' :=
                                unary_transport classifierUnary sameClassifier
                              have sameControw : hsame controw controw' :=
                                cont_respects_hsame (hsame_refl embedding) sameLedger ledgerCont
                                  targetLedgerCont
                              have samePkgrow : hsame pkgrow pkgrow' :=
                                cont_respects_hsame sameControw sameClassifier pkgCont targetPkgCont
                              exact And.intro
                                (And.intro numfieldUnary
                                  (And.intro introwUnary
                                      (And.intro embeddingUnary
                                        (And.intro ledgerUnary'
                                          (And.intro classifierUnary'
                                            (And.intro targetLedgerCont
                                              (And.intro targetPkgCont targetPkgSig)))))))
                                (And.intro sameControw samePkgrow)

def RingOfIntegersClassifierTransportCarrier [AskSetup] [PackageSetup]
    (num embedded embedding equation classifier contRow provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  IntCarrier BEDC.FKernel.Mark.BMark.b0 embedded ∧ Cont embedded num embedding ∧
    Cont embedding equation contRow ∧ hsame classifier contRow ∧
      Cont provenance contRow endpoint ∧ PkgSig bundle endpoint pkg

theorem RingOfIntegersDedekindSourceCarrier_classifier_transport [AskSetup] [PackageSetup]
    {num embedded embedding equation classifier contRow provenance endpoint embedded'
      embedding' contRow' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersClassifierTransportCarrier num embedded embedding equation classifier contRow
        provenance endpoint bundle pkg ->
      hsame embedded embedded' ->
        Cont embedded' num embedding' ->
          Cont embedding' equation contRow' ->
            Cont provenance contRow' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                RingOfIntegersClassifierTransportCarrier num embedded' embedding' equation
                    classifier contRow' provenance endpoint' bundle pkg ∧
                  hsame embedding embedding' ∧ hsame contRow contRow' := by
  intro carrier sameEmbedded embeddingCont' contRowCont' endpointCont' pkgSig'
  have embeddedCarrier' :
      IntCarrier BEDC.FKernel.Mark.BMark.b0 embedded' :=
    IntCarrier_magnitude_hsame_transport carrier.left sameEmbedded
  have sameEmbedding : hsame embedding embedding' :=
    cont_respects_hsame sameEmbedded (hsame_refl num) carrier.right.left embeddingCont'
  have sameContRow : hsame contRow contRow' :=
    cont_respects_hsame sameEmbedding (hsame_refl equation) carrier.right.right.left
      contRowCont'
  have sameClassifierContRow' : hsame classifier contRow' :=
    hsame_trans carrier.right.right.right.left sameContRow
  have carrier' :
      RingOfIntegersClassifierTransportCarrier num embedded' embedding' equation classifier
        contRow' provenance endpoint' bundle pkg :=
    And.intro embeddedCarrier'
      (And.intro embeddingCont'
        (And.intro contRowCont'
          (And.intro sameClassifierContRow'
            (And.intro endpointCont' pkgSig'))))
  exact And.intro carrier' (And.intro sameEmbedding sameContRow)

end BEDC.Derived.RingOfIntegersUp
