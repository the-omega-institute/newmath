import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RingOfIntegersDedekindSourceCarrier [AskSetup] [PackageSetup]
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
    RingOfIntegersDedekindSourceCarrier numfield introw embedding ledger classifier controw
        pkgrow bundle pkg ->
      hsame ledger ledger' ->
        hsame classifier classifier' ->
          Cont embedding ledger' controw' ->
            Cont controw' classifier' pkgrow' ->
              PkgSig bundle pkgrow' pkg ->
                RingOfIntegersDedekindSourceCarrier numfield introw embedding ledger'
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

theorem RingOfIntegersDedekindSourceCarrier_root_classifier_transport
    [AskSetup] [PackageSetup]
    {numfield introw embedding ledger classifier controw pkgrow classifier' pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersDedekindSourceCarrier numfield introw embedding ledger classifier controw
        pkgrow bundle pkg ->
      hsame classifier classifier' ->
        Cont controw classifier' pkgrow' ->
          PkgSig bundle pkgrow' pkg ->
            RingOfIntegersDedekindSourceCarrier numfield introw embedding ledger classifier'
                controw pkgrow' bundle pkg ∧
              hsame pkgrow pkgrow' := by
  intro carrier sameClassifier targetPkgCont targetPkgSig
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
                              have classifierUnary' : UnaryHistory classifier' :=
                                unary_transport classifierUnary sameClassifier
                              have samePkgrow : hsame pkgrow pkgrow' :=
                                cont_respects_hsame (hsame_refl controw) sameClassifier pkgCont
                                  targetPkgCont
                              exact And.intro
                                (And.intro numfieldUnary
                                  (And.intro introwUnary
                                    (And.intro embeddingUnary
                                      (And.intro ledgerUnary
                                        (And.intro classifierUnary'
                                          (And.intro ledgerCont
                                            (And.intro targetPkgCont targetPkgSig)))))))
                                samePkgrow

end BEDC.Derived.RingOfIntegersUp
