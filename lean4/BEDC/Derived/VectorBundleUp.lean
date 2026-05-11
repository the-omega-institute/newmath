import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VectorBundleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def VectorBundleFiniteCarrier [AskSetup] [PackageSetup]
    (bundle vecspace trivialization fiber transition classifier contRows provenance : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundle ∧ UnaryHistory vecspace ∧ UnaryHistory trivialization ∧
    UnaryHistory fiber ∧ UnaryHistory transition ∧ UnaryHistory classifier ∧
      UnaryHistory contRows ∧ Cont bundle vecspace trivialization ∧
        Cont fiber transition classifier ∧ Cont trivialization classifier contRows ∧
          PkgSig probe provenance pkg

theorem VectorBundleFiniteCarrier_classifier_stability_obligation [AskSetup] [PackageSetup]
    {bundle vecspace trivialization fiber transition classifier contRows provenance bundle'
      vecspace' trivialization' fiber' transition' classifier' contRows' provenance' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    VectorBundleFiniteCarrier bundle vecspace trivialization fiber transition classifier contRows
        provenance probe pkg ->
      hsame bundle bundle' ->
      hsame vecspace vecspace' ->
      hsame trivialization trivialization' ->
      hsame fiber fiber' ->
      hsame transition transition' ->
      Cont bundle' vecspace' trivialization' ->
      Cont fiber' transition' classifier' ->
      Cont trivialization' classifier' contRows' ->
      PkgSig probe provenance' pkg ->
      VectorBundleFiniteCarrier bundle' vecspace' trivialization' fiber' transition'
          classifier' contRows' provenance' probe pkg ∧
        hsame classifier classifier' ∧ hsame contRows contRows' := by
  intro carrier sameBundle sameVecspace sameTrivialization sameFiber sameTransition
    bundleVecspaceRow fiberTransitionRow trivializationClassifierRow pkgRow
  obtain ⟨bundleUnary, vecspaceUnary, trivializationUnary, fiberUnary, transitionUnary,
    classifierUnary, contRowsUnary, oldBundleVecspaceRow, oldFiberTransitionRow,
    oldTrivializationClassifierRow, _oldPkgRow⟩ := carrier
  have bundleUnary' : UnaryHistory bundle' :=
    unary_transport bundleUnary sameBundle
  have vecspaceUnary' : UnaryHistory vecspace' :=
    unary_transport vecspaceUnary sameVecspace
  have trivializationUnary' : UnaryHistory trivialization' :=
    unary_cont_closed bundleUnary' vecspaceUnary' bundleVecspaceRow
  have fiberUnary' : UnaryHistory fiber' :=
    unary_transport fiberUnary sameFiber
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed fiberUnary' transitionUnary' fiberTransitionRow
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_cont_closed trivializationUnary' classifierUnary' trivializationClassifierRow
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameFiber sameTransition oldFiberTransitionRow fiberTransitionRow
  have sameContRows : hsame contRows contRows' :=
    cont_respects_hsame sameTrivialization sameClassifier oldTrivializationClassifierRow
      trivializationClassifierRow
  exact And.intro
    (And.intro bundleUnary'
      (And.intro vecspaceUnary'
        (And.intro trivializationUnary'
          (And.intro fiberUnary'
            (And.intro transitionUnary'
              (And.intro classifierUnary'
                (And.intro contRowsUnary'
                  (And.intro bundleVecspaceRow
                    (And.intro fiberTransitionRow
                      (And.intro trivializationClassifierRow pkgRow))))))))))
    (And.intro sameClassifier sameContRows)

end BEDC.Derived.VectorBundleUp
