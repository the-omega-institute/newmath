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

theorem Gamma_holomorphic_limit_certificate_readback {s z : BHist} :
    Gamma s z ->
      ∃ apart : BHist, ∃ P : BHist -> BHist, ∃ N : BHist -> BHist,
        ∃ M : BHist -> BHist,
          GammaDomainCore s apart ∧ UnaryHistory apart ∧
            GammaWeierstrassCauchyModulus s apart P N ∧ ComplexLimit P N z M ∧
              ComplexHistoryCarrier z := by
  intro gamma
  cases gamma with
  | intro apart gammaData =>
      cases gammaData with
      | intro P gammaData =>
          cases gammaData with
          | intro N gammaData =>
              cases gammaData with
              | intro M rows =>
                  exact Exists.intro apart
                    (Exists.intro P
                      (Exists.intro N
                        (Exists.intro M
                          (And.intro rows.left
                            (And.intro rows.right.left
                              (And.intro rows.right.right.left
                                (And.intro rows.right.right.right
                                  rows.right.right.right.right.left)))))))

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

theorem Gamma_reflection_boundary_certificate_data {s t z w : BHist} :
    Gamma s z -> Gamma t w ->
      exists apartS : BHist, exists apartT : BHist, exists P : BHist -> BHist,
      exists N : BHist -> BHist, exists M : BHist -> BHist,
      exists Q : BHist -> BHist, exists R : BHist -> BHist,
      exists L : BHist -> BHist,
        GammaDomainCore s apartS ∧ GammaDomainCore t apartT ∧
          GammaWeierstrassCauchyModulus s apartS P N ∧
          GammaWeierstrassCauchyModulus t apartT Q R ∧
          ComplexLimit P N z M ∧ ComplexLimit Q R w L ∧
          ComplexHistoryCarrier z ∧ ComplexHistoryCarrier w ∧
          ComplexHistoryCarrier (append z w) ∧ Cont z w (append z w) := by
  intro gammaS gammaT
  cases gammaS with
  | intro apartS gammaSRest =>
      cases gammaSRest with
      | intro P gammaSRest =>
          cases gammaSRest with
          | intro N gammaSRest =>
              cases gammaSRest with
              | intro M gammaSData =>
                  cases gammaSData with
                  | intro domainS gammaSData =>
                      cases gammaSData with
                      | intro _apartSUnary gammaSData =>
                          cases gammaSData with
                          | intro modulusS limitS =>
                              cases gammaT with
                              | intro apartT gammaTRest =>
                                  cases gammaTRest with
                                  | intro Q gammaTRest =>
                                      cases gammaTRest with
                                      | intro R gammaTRest =>
                                          cases gammaTRest with
                                          | intro L gammaTData =>
                                              cases gammaTData with
                                              | intro domainT gammaTData =>
                                                  cases gammaTData with
                                                  | intro _apartTUnary gammaTData =>
                                                      cases gammaTData with
                                                      | intro modulusT limitT =>
                                                          have carrierZ :
                                                              ComplexHistoryCarrier z :=
                                                            limitS.right.left
                                                          have carrierW :
                                                              ComplexHistoryCarrier w :=
                                                            limitT.right.left
                                                          have carrierAppend :
                                                              ComplexHistoryCarrier
                                                                (append z w) :=
                                                            ComplexHistoryCarrier_append_unary_closed
                                                              carrierZ
                                                              (ComplexHistoryCarrier_unary
                                                                carrierW)
                                                          exact Exists.intro apartS
                                                            (Exists.intro apartT
                                                              (Exists.intro P
                                                                (Exists.intro N
                                                                  (Exists.intro M
                                                                    (Exists.intro Q
                                                                      (Exists.intro R
                                                                        (Exists.intro L
                                                                          (And.intro domainS
                                                                            (And.intro domainT
                                                                              (And.intro modulusS
                                                                                (And.intro modulusT
                                                                                  (And.intro limitS
                                                                                    (And.intro limitT
                                                                                      (And.intro carrierZ
                                                                                        (And.intro carrierW
                                                                                          (And.intro carrierAppend
                                                                                            (cont_intro rfl)))))))))))))))))

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

theorem Gamma_reflection_boundary_certificate {s t z w : BHist} :
    Gamma s z -> Gamma t w ->
      ∃ apartS : BHist, ∃ apartT : BHist,
        ∃ PS : BHist -> BHist, ∃ NS : BHist -> BHist, ∃ MS : BHist -> BHist,
          ∃ PT : BHist -> BHist, ∃ NT : BHist -> BHist, ∃ MT : BHist -> BHist,
            GammaDomainCore s apartS ∧ UnaryHistory apartS ∧
              GammaWeierstrassCauchyModulus s apartS PS NS ∧
                ComplexLimit PS NS z MS ∧
                  GammaDomainCore t apartT ∧ UnaryHistory apartT ∧
                    GammaWeierstrassCauchyModulus t apartT PT NT ∧
                      ComplexLimit PT NT w MT := by
  intro gammaS gammaT
  cases gammaS with
  | intro apartS gammaSData =>
      cases gammaSData with
      | intro PS gammaSData =>
          cases gammaSData with
          | intro NS gammaSData =>
              cases gammaSData with
              | intro MS gammaSRows =>
                  cases gammaT with
                  | intro apartT gammaTData =>
                      cases gammaTData with
                      | intro PT gammaTData =>
                          cases gammaTData with
                          | intro NT gammaTData =>
                              cases gammaTData with
                              | intro MT gammaTRows =>
                                  exact ⟨apartS, apartT, PS, NS, MS, PT, NT, MT,
                                    gammaSRows.left, gammaSRows.right.left,
                                    gammaSRows.right.right.left,
                                    gammaSRows.right.right.right, gammaTRows.left,
                                    gammaTRows.right.left, gammaTRows.right.right.left,
                                    gammaTRows.right.right.right⟩

end BEDC.Derived.GammaFunctionUp
