import BEDC.Derived.GammaUp
import BEDC.Derived.ComplexLimitUp
import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.GammaFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.GammaUp
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.ComplexSeriesUp

def GammaWeierstrassCauchyModulus
    (s apart : BHist) (P N : BHist -> BHist) : Prop :=
  GammaDomainCore s apart ∧ ComplexRegularSequence P N

def GammaWeierstrassPart (s apart n p : BHist) : Prop :=
  GammaDomainCore s apart ∧ UnaryHistory n ∧ ComplexHistoryCarrier p ∧
    ComplexPartSum BHist.Empty (fun k : BHist => append s k) n p

def Gamma (s z : BHist) : Prop :=
  ∃ apart : BHist, ∃ P N M : BHist -> BHist,
    GammaDomainCore s apart ∧ UnaryHistory apart ∧
      GammaWeierstrassCauchyModulus s apart P N ∧ ComplexLimit P N z M

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
