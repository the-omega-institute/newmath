import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SplittingFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SplittingFieldRootCarrierPacket [AskSetup] [PackageSetup]
    (fieldext polynomial roots factors controw transport pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldext ∧ UnaryHistory polynomial ∧ UnaryHistory roots ∧
    UnaryHistory factors ∧ UnaryHistory transport ∧ Cont roots factors controw ∧
      Cont controw transport pkgrow ∧ PkgSig bundle pkgrow pkg

theorem SplittingFieldRootCarrierPacket_root_classifier_transport [AskSetup] [PackageSetup]
    {fieldext polynomial roots factors controw transport pkgrow roots' factors' controw'
      transport' pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SplittingFieldRootCarrierPacket fieldext polynomial roots factors controw transport pkgrow
        bundle pkg ->
      hsame roots roots' ->
        hsame factors factors' ->
          hsame transport transport' ->
            Cont roots' factors' controw' ->
              Cont controw' transport' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  SplittingFieldRootCarrierPacket fieldext polynomial roots' factors' controw'
                      transport' pkgrow' bundle pkg ∧
                    hsame controw controw' ∧ hsame pkgrow pkgrow' := by
  intro carrier sameRoots sameFactors sameTransport targetRootCont targetPkgCont targetPkgSig
  cases carrier with
  | intro fieldextUnary rest =>
      cases rest with
      | intro polynomialUnary rest =>
          cases rest with
          | intro rootsUnary rest =>
              cases rest with
              | intro factorsUnary rest =>
                  cases rest with
                  | intro transportUnary rest =>
                      cases rest with
                      | intro rootCont rest =>
                          cases rest with
                          | intro pkgCont _ =>
                              have rootsUnary' : UnaryHistory roots' :=
                                unary_transport rootsUnary sameRoots
                              have factorsUnary' : UnaryHistory factors' :=
                                unary_transport factorsUnary sameFactors
                              have transportUnary' : UnaryHistory transport' :=
                                unary_transport transportUnary sameTransport
                              have sameControw : hsame controw controw' :=
                                cont_respects_hsame sameRoots sameFactors rootCont targetRootCont
                              have samePkgrow : hsame pkgrow pkgrow' :=
                                cont_respects_hsame sameControw sameTransport pkgCont targetPkgCont
                              exact And.intro
                                (And.intro fieldextUnary
                                  (And.intro polynomialUnary
                                    (And.intro rootsUnary'
                                      (And.intro factorsUnary'
                                        (And.intro transportUnary'
                                          (And.intro targetRootCont
                                            (And.intro targetPkgCont targetPkgSig)))))))
                                (And.intro sameControw samePkgrow)

end BEDC.Derived.SplittingFieldUp
