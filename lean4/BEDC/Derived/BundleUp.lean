import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive BundleLocalTrivBundle : ProbeBundle BHist -> Prop where
  | bnil : BundleLocalTrivBundle .Bnil
  | bcons {row : BHist} {tail : ProbeBundle BHist} :
      UnaryHistory row -> BundleLocalTrivBundle tail ->
        BundleLocalTrivBundle (.Bcons row tail)

inductive BundleLocalTrivBundleClassifier :
    ProbeBundle BHist -> ProbeBundle BHist -> Prop where
  | bnil : BundleLocalTrivBundleClassifier .Bnil .Bnil
  | bcons {row row' : BHist} {tail tail' : ProbeBundle BHist} :
      hsame row row' -> BundleLocalTrivBundleClassifier tail tail' ->
        BundleLocalTrivBundleClassifier (.Bcons row tail) (.Bcons row' tail')

def BundleLocalTrivPackage
    (base total projection fibre : BHist) (triv : ProbeBundle BHist)
    (transition ledger : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    BundleLocalTrivBundle triv ∧ UnaryHistory transition ∧ UnaryHistory ledger ∧
      Cont base total projection ∧ Cont projection fibre transition ∧
        Cont transition ledger total

def BundleLocalTrivClassifier
    (base total projection fibre : BHist) (triv : ProbeBundle BHist)
    (transition ledger base' total' projection' fibre' : BHist) (triv' : ProbeBundle BHist)
    (transition' ledger' : BHist) : Prop :=
  hsame base base' ∧ hsame total total' ∧ hsame projection projection' ∧
    hsame fibre fibre' ∧ BundleLocalTrivBundleClassifier triv triv' ∧
      hsame transition transition' ∧ hsame ledger ledger'

theorem BundleLocalTrivBundle_classifier_transport {triv triv' : ProbeBundle BHist} :
    BundleLocalTrivBundle triv -> BundleLocalTrivBundleClassifier triv triv' ->
      BundleLocalTrivBundle triv' := by
  intro bundle classified
  induction classified with
  | bnil =>
      exact BundleLocalTrivBundle.bnil
  | bcons sameRow sameTail ih =>
      cases bundle with
      | bcons rowUnary tailBundle =>
          exact BundleLocalTrivBundle.bcons (unary_transport rowUnary sameRow)
            (ih tailBundle)

theorem BundleLocalTrivPackage_classifier_transport
    {base total projection fibre transition ledger base' total' projection' fibre' transition'
      ledger' : BHist}
    {triv triv' : ProbeBundle BHist} :
    BundleLocalTrivPackage base total projection fibre triv transition ledger ->
      BundleLocalTrivClassifier base total projection fibre triv transition ledger base' total'
        projection' fibre' triv' transition' ledger' ->
        BundleLocalTrivPackage base' total' projection' fibre' triv' transition' ledger' ∧
          Cont base' total' projection' ∧ Cont projection' fibre' transition' := by
  intro package classified
  have sameBase : hsame base base' := classified.left
  have sameTotal : hsame total total' := classified.right.left
  have sameProjection : hsame projection projection' := classified.right.right.left
  have sameFibre : hsame fibre fibre' := classified.right.right.right.left
  have sameTriv : BundleLocalTrivBundleClassifier triv triv' :=
    classified.right.right.right.right.left
  have sameTransition : hsame transition transition' :=
    classified.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    classified.right.right.right.right.right.right
  have baseUnary : UnaryHistory base := package.left
  have totalUnary : UnaryHistory total := package.right.left
  have projectionUnary : UnaryHistory projection := package.right.right.left
  have fibreUnary : UnaryHistory fibre := package.right.right.right.left
  have trivRows : BundleLocalTrivBundle triv := package.right.right.right.right.left
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger := package.right.right.right.right.right.right.left
  have projectionRow : Cont base total projection :=
    package.right.right.right.right.right.right.right.left
  have transitionRow : Cont projection fibre transition :=
    package.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont transition ledger total :=
    package.right.right.right.right.right.right.right.right.right
  have baseUnary' : UnaryHistory base' := unary_transport baseUnary sameBase
  have totalUnary' : UnaryHistory total' := unary_transport totalUnary sameTotal
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport projectionUnary sameProjection
  have fibreUnary' : UnaryHistory fibre' := unary_transport fibreUnary sameFibre
  have trivRows' : BundleLocalTrivBundle triv' :=
    BundleLocalTrivBundle_classifier_transport trivRows sameTriv
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have ledgerUnary' : UnaryHistory ledger' := unary_transport ledgerUnary sameLedger
  have projectionRow' : Cont base' total' projection' := by
    cases sameBase
    cases sameTotal
    cases sameProjection
    exact projectionRow
  have transitionRow' : Cont projection' fibre' transition' := by
    cases sameProjection
    cases sameFibre
    cases sameTransition
    exact transitionRow
  have ledgerRow' : Cont transition' ledger' total' := by
    cases sameTransition
    cases sameLedger
    cases sameTotal
    exact ledgerRow
  have package' :
      BundleLocalTrivPackage base' total' projection' fibre' triv' transition' ledger' :=
    And.intro baseUnary'
      (And.intro totalUnary'
        (And.intro projectionUnary'
          (And.intro fibreUnary'
            (And.intro trivRows'
              (And.intro transitionUnary'
                (And.intro ledgerUnary'
                  (And.intro projectionRow'
                    (And.intro transitionRow' ledgerRow'))))))))
  exact And.intro package' (And.intro projectionRow' transitionRow')

end BEDC.Derived.BundleUp
