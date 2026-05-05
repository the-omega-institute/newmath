import BEDC.Derived.GammaUp
import BEDC.Derived.ComplexLimitUp
import BEDC.Derived.ComplexSeriesUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.GammaFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GammaUp
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.ComplexSeriesUp

def GammaWeierstrassCauchyModulus
    (s apart : BHist) (P N : BHist -> BHist) : Prop :=
  GammaDomainCore s apart ∧ ComplexRegularSequence P N

theorem GammaWeierstrassCauchyModulus_constant {s apart z : BHist} :
    GammaDomainCore s apart -> ComplexHistoryCarrier z ->
      GammaWeierstrassCauchyModulus s apart (fun _ : BHist => z)
        (fun _ : BHist => BHist.Empty) := by
  intro domain carrierZ
  have zUnary : UnaryHistory z := ComplexHistoryCarrier_unary carrierZ
  exact And.intro domain (ComplexRegularSequence_constant zUnary)

def GammaWeierstrassPart (s apart n p : BHist) : Prop :=
  GammaDomainCore s apart ∧ UnaryHistory n ∧ ComplexHistoryCarrier p ∧
    ComplexPartSum BHist.Empty (fun k : BHist => append s k) n p

def Gamma (s z : BHist) : Prop :=
  ∃ apart : BHist, ∃ P N M : BHist -> BHist,
    GammaDomainCore s apart ∧ UnaryHistory apart ∧
      GammaWeierstrassCauchyModulus s apart P N ∧ ComplexLimit P N z M

theorem Gamma_recurrence_limit_pair_carriers {s z w : BHist} :
    Gamma s z -> Gamma (append s (BHist.e1 BHist.Empty)) w ->
      (exists apart : BHist,
        GammaDomainCore s apart ∧ UnaryHistory apart ∧ ComplexHistoryCarrier z) ∧
        (exists apartShift : BHist,
          GammaDomainCore (append s (BHist.e1 BHist.Empty)) apartShift ∧
            UnaryHistory apartShift ∧ ComplexHistoryCarrier w) := by
  intro gammaS gammaShift
  cases gammaS with
  | intro apart gammaRest =>
      cases gammaRest with
      | intro P gammaRest =>
          cases gammaRest with
          | intro N gammaRest =>
              cases gammaRest with
              | intro M gammaData =>
                  cases gammaShift with
                  | intro apartShift shiftedRest =>
                      cases shiftedRest with
                      | intro PShift shiftedRest =>
                          cases shiftedRest with
                          | intro NShift shiftedRest =>
                              cases shiftedRest with
                              | intro MShift shiftedData =>
                                  exact And.intro
                                    (Exists.intro apart
                                      (And.intro gammaData.left
                                        (And.intro gammaData.right.left
                                          gammaData.right.right.right.right.left)))
                                    (Exists.intro apartShift
                                      (And.intro shiftedData.left
                                        (And.intro shiftedData.right.left
                                          shiftedData.right.right.right.right.left)))

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

theorem gamma_function_semantic_name_certificate {s z : BHist} (gamma : Gamma s z) :
    SemanticNameCert (fun result : BHist => Gamma s result)
      (fun result : BHist => Gamma s result)
      (fun result : BHist => Gamma s result) hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro z gamma
      equiv_refl := by
        intro result _source
        exact hsame_refl result
      equiv_symm := by
        intro result result' sameResult
        exact hsame_symm sameResult
      equiv_trans := by
        intro result result' result'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro result result' sameResult source
        cases sameResult
        exact source
    }
    pattern_sound := by
      intro result source
      exact source
    ledger_sound := by
      intro result source
      exact source
  }

end BEDC.Derived.GammaFunctionUp
