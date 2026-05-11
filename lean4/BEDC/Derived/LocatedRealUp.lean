import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealCarrierSurface [AskSetup] [PackageSetup]
    (regseq interval schedule classifier pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regseq ∧ UnaryHistory interval ∧ UnaryHistory schedule ∧
    UnaryHistory classifier ∧ UnaryHistory pkgrow ∧ Cont regseq schedule classifier ∧
      Cont interval classifier pkgrow ∧ PkgSig bundle pkgrow pkg

theorem LocatedRealCarrierSurface_regseqrat_classifier_stability [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow regseq' interval' schedule' classifier'
      pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      hsame regseq regseq' ->
        hsame interval interval' ->
          hsame schedule schedule' ->
            Cont regseq' schedule' classifier' ->
              Cont interval' classifier' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow'
                      bundle pkg ∧
                    hsame classifier classifier' ∧ hsame pkgrow pkgrow' := by
  intro surface sameRegseq sameInterval sameSchedule classifierRoute' pkgrowRoute' pkgrowSig'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameRegseq sameSchedule surface.right.right.right.right.right.left
      classifierRoute'
  have samePkgrow : hsame pkgrow pkgrow' :=
    cont_respects_hsame sameInterval sameClassifier surface.right.right.right.right.right.right.left
      pkgrowRoute'
  have transported :
      LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow' bundle pkg :=
    ⟨unary_transport surface.left sameRegseq,
      unary_transport surface.right.left sameInterval,
      unary_transport surface.right.right.left sameSchedule,
      unary_transport surface.right.right.right.left sameClassifier,
      unary_transport surface.right.right.right.right.left samePkgrow,
      classifierRoute',
      pkgrowRoute',
      pkgrowSig'⟩
  exact And.intro transported (And.intro sameClassifier samePkgrow)

end BEDC.Derived.LocatedRealUp
