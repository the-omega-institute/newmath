import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

def BetaSubstitutionPreservation : Prop :=
  ∀ {Γ : Ctx} {dom body arg cod : Term},
    HasType ((shift 0 1 dom) :: Γ) body cod →
    HasType Γ arg dom →
    HasType Γ (substitute 0 arg body) (substitute 0 arg cod)

def LamDomainSubjectReduction : Prop :=
  ∀ {Γ : Ctx} {d d' b A : Term},
    HasType Γ (Term.lam d b) A →
    BetaStep d d' →
    HasType Γ (Term.lam d' b) A

def PiDomainSubjectReduction : Prop :=
  ∀ {Γ : Ctx} {d d' c A : Term},
    HasType Γ (Term.pi d c) A →
    BetaStep d d' →
    HasType Γ (Term.pi d' c) A

def AppArgTypeStable : Prop :=
  ∀ {Γ : Ctx} {f a a' dom cod : Term},
    HasType Γ f (Term.pi dom cod) →
    HasType Γ a dom →
    HasType Γ a' dom →
    substitute 0 a' cod = substitute 0 a cod

end BEDC.MetaCIC
