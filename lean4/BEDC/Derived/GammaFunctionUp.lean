import BEDC.Derived.GammaUp
import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.GammaFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GammaUp
open BEDC.Derived.ComplexLimitUp

def GammaWeierstrassCauchyModulus
    (s apart : BHist) (P N : BHist -> BHist) : Prop :=
  GammaDomainCore s apart ∧ ComplexRegularSequence P N

theorem GammaWeierstrassCauchyModulus_hsame_transport
    {s t apart : BHist} {P Q N : BHist -> BHist}
    (sameST : hsame s t)
    (pointwise : forall {n : BHist}, UnaryHistory n -> hsame (P n) (Q n)) :
    GammaWeierstrassCauchyModulus s apart P N ->
      GammaWeierstrassCauchyModulus t apart Q N := by
  intro modulus
  exact And.intro (GammaDomainCore_hsame_transport sameST modulus.left).left
    (ComplexRegularSequence_hsame_transport pointwise modulus.right)

theorem GammaLimitCertificate_hsame_transport
    {s t apart z : BHist} {P Q N M : BHist -> BHist}
    (sameST : hsame s t)
    (pointwise : forall {n : BHist}, UnaryHistory n -> hsame (P n) (Q n)) :
    GammaDomainCore s apart -> ComplexLimit P N z M ->
      GammaDomainCore t apart ∧ ComplexLimit Q N z M := by
  intro domain limit
  exact And.intro (GammaDomainCore_hsame_transport sameST domain).left
    (ComplexLimit_sequence_hsame_transport pointwise limit)

end BEDC.Derived.GammaFunctionUp
