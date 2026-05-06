import BEDC.FKernel.Cont

namespace BEDC.Derived.OdeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def OdeLocalFlowRow (t0 x0 t1 x1 v p ell : BHist) : Prop :=
  Cont t0 x0 p ∧ Cont p v ell ∧ Cont t1 ell x1

theorem OdeLocalFlowRow_picard_continuation_scope
    {t0 x0 t1 x1 v p ell next route : BHist} :
    OdeLocalFlowRow t0 x0 t1 x1 v p ell -> Cont x1 next route ->
      exists carried : BHist, Cont ell next carried ∧ Cont t1 carried route := by
  intro row endpoint
  exact cont_assoc_left_exists row.right.right endpoint

theorem OdeLocalFlow_endpoint_classifier_deterministic
    {t0 x0 p p' v v' ell ell' t1 x1 x1' : BHist} :
    Cont t0 x0 p ->
      Cont t0 x0 p' ->
        hsame v v' ->
          Cont p v ell ->
            Cont p' v' ell' ->
              Cont t1 ell x1 ->
                Cont t1 ell' x1' -> hsame x1 x1' := by
  intro initial initial' vectorSame step step' endpoint endpoint'
  have picardSame : hsame p p' := cont_deterministic initial initial'
  have localSame : hsame ell ell' :=
    cont_respects_hsame picardSame vectorSame step step'
  exact cont_respects_hsame (hsame_refl t1) localSame endpoint endpoint'

end BEDC.Derived.OdeUp
