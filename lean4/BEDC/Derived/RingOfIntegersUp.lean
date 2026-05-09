import BEDC.Derived.NumFieldUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.RingOfIntegersUp

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

end BEDC.Derived.RingOfIntegersUp
