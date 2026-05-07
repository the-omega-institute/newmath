import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PdeRelationClassifier
    (manifold derivative relation boundary provenance : BHist) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory boundary ∧
    Cont manifold derivative relation ∧ Cont relation boundary provenance

theorem PdeRelationClassifier_endpoint_transport
    {manifold manifold' derivative derivative' relation relation' boundary boundary' provenance
      provenance' : BHist} :
    PdeRelationClassifier manifold derivative relation boundary provenance ->
      hsame manifold manifold' -> hsame derivative derivative' -> hsame boundary boundary' ->
        Cont manifold' derivative' relation' -> Cont relation' boundary' provenance' ->
          PdeRelationClassifier manifold' derivative' relation' boundary' provenance' ∧
            hsame relation relation' ∧ hsame provenance provenance' := by
  intro rows sameManifold sameDerivative sameBoundary transportedRelation transportedProvenance
  have relationSame : hsame relation relation' :=
    cont_respects_hsame sameManifold sameDerivative rows.right.right.right.left
      transportedRelation
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame relationSame sameBoundary rows.right.right.right.right
      transportedProvenance
  have transportedRows :
      PdeRelationClassifier manifold' derivative' relation' boundary' provenance' :=
    And.intro (unary_transport rows.left sameManifold)
      (And.intro (unary_transport rows.right.left sameDerivative)
        (And.intro (unary_transport rows.right.right.left sameBoundary)
          (And.intro transportedRelation transportedProvenance)))
  exact And.intro transportedRows (And.intro relationSame provenanceSame)

end BEDC.Derived.PdeUp
