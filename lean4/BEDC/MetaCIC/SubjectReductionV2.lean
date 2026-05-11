import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.TypingV2

namespace BEDC.MetaCIC.V2

def BetaSubstitutionPreservationV2 : Prop :=
  ∀ {Γ : Ctx} {dom body arg cod : Term},
    HasTypeV2 ((shift 0 1 dom) :: Γ) body cod →
    HasTypeV2 Γ arg dom →
    HasTypeV2 Γ (substitute 0 arg body) (substitute 0 arg cod)

theorem subject_reduction_V2_beta
    (hsubst : BetaSubstitutionPreservationV2)
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasTypeV2 Γ (Term.app (Term.lam dom body) arg) A) :
    HasTypeV2 Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact hsubst hbody ha

end BEDC.MetaCIC.V2
