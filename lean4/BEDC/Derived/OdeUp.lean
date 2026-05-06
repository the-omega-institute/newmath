import BEDC.FKernel.Cont

namespace BEDC.Derived.OdeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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
