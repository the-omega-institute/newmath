import BEDC.Derived.ContinuousUp.Transport
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ContinuousSourceSpec (source : BHist) : Prop :=
  UnaryHistory source ∧
    ∃ map target modulus cert : BHist, ContinuousFunctionCarrier source map target modulus cert

def ContinuousFunctionPatternSpec (source map target modulus cert : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory map ∧ UnaryHistory modulus ∧
    ContinuousModulusWitness target modulus cert ∧ Cont source map target

theorem ContinuousFunctionCarrier_sourceSpec_readback
    {source map target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert -> ContinuousSourceSpec source := by
  intro carrier
  exact And.intro carrier.left
    (Exists.intro map
      (Exists.intro target
        (Exists.intro modulus
          (Exists.intro cert carrier))))

theorem ContinuousFunctionPatternSpec_function_carrier_iff
    {source map target modulus cert : BHist} :
    ContinuousFunctionPatternSpec source map target modulus cert ↔
      ContinuousFunctionCarrier source map target modulus cert ∧ UnaryHistory cert := by
  constructor
  · intro pattern
    cases pattern with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro mapCarrier rest =>
                cases rest with
                | intro modulusCarrier rest =>
                    cases rest with
                    | intro modulusWitness sourceMap =>
                        exact
                          And.intro
                            (And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro mapCarrier
                                  (And.intro modulusCarrier
                                    (And.intro sourceMap
                                      modulusWitness.right.right.right)))))
                            modulusWitness.right.right.left
  · intro carrierData
    cases carrierData with
    | intro carrier certCarrier =>
        cases carrier with
        | intro sourceCarrier rest =>
            cases rest with
            | intro targetCarrier rest =>
                cases rest with
                | intro mapCarrier rest =>
                    cases rest with
                    | intro modulusCarrier rest =>
                        cases rest with
                        | intro sourceMap targetCert =>
                            exact
                              And.intro sourceCarrier
                                (And.intro targetCarrier
                                  (And.intro mapCarrier
                                    (And.intro modulusCarrier
                                      (And.intro
                                        (And.intro targetCarrier
                                          (And.intro modulusCarrier
                                            (And.intro certCarrier targetCert)))
                                        sourceMap))))

theorem ContinuousFunctionCarrier_certificate_semanticNameCert
    {source map target modulus cert : BHist}
    (carrier : ContinuousFunctionCarrier source map target modulus cert) :
    SemanticNameCert (fun c : BHist => ContinuousFunctionCarrier source map target modulus c)
      (fun c : BHist => ContinuousFunctionCarrier source map target modulus c)
      (fun c : BHist => ContinuousFunctionCarrier source map target modulus c) hsame := by
  constructor
  · constructor
    · exact Exists.intro cert carrier
    · intro c _displayed
      exact hsame_refl c
    · intro c c' same
      exact hsame_symm same
    · intro c c' c'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro c c' same displayed
      exact
        ContinuousFunctionCarrier_hsame_transport (hsame_refl source) (hsame_refl map)
          (hsame_refl target) (hsame_refl modulus) same displayed
  · intro _c displayed
    exact displayed
  · intro _c displayed
    exact displayed

theorem ContinuousUp_StdBridge {source map target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert ->
      ContinuousSourceSpec source ∧
        ContinuousFunctionPatternSpec source map target modulus cert ∧
          SemanticNameCert
            (fun c : BHist => ContinuousFunctionCarrier source map target modulus c)
            (fun c : BHist => ContinuousFunctionCarrier source map target modulus c)
            (fun c : BHist => ContinuousFunctionCarrier source map target modulus c) hsame := by
  intro carrier
  have certCarrier : UnaryHistory cert :=
    unary_cont_closed carrier.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right
  have patternSpec : ContinuousFunctionPatternSpec source map target modulus cert :=
    (ContinuousFunctionPatternSpec_function_carrier_iff.mpr (And.intro carrier certCarrier))
  exact And.intro (ContinuousFunctionCarrier_sourceSpec_readback carrier)
    (And.intro patternSpec (ContinuousFunctionCarrier_certificate_semanticNameCert carrier))

end BEDC.Derived.ContinuousUp
