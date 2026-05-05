import BEDC.Derived.ContinuousUp.SourceRestriction
import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_empty_source_restriction_terminal_modulus_commutes
    {p q restricted source map target modulus cert extra modulus' cert' displayedTarget
      displayedCert : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
        ContinuousModulusWitness cert extra cert' -> Cont modulus extra modulus' ->
          ContinuousFunctionCarrier (append p restricted) map (append p displayedTarget)
            (append modulus' q) (append (append p displayedCert) q) ->
            hsame target displayedTarget ∧ hsame cert' displayedCert := by
  intro sourceRestriction visibleCarrier terminalWitness modulusRel displayedCarrier
  have carrierData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp visibleCarrier
  have displayedData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := restricted) (map := map) (target := displayedTarget) (modulus := modulus')
      (cert := displayedCert)).mp displayedCarrier
  exact
    ContinuousFunctionCarrier_empty_source_restriction_terminal_modulus_commutes
      sourceRestriction carrierData.right.right terminalWitness modulusRel displayedData.right.right

end BEDC.Derived.ContinuousUp
