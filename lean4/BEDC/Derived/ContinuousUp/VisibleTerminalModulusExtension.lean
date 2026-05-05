import BEDC.Derived.ContinuousUp.Suffix
import BEDC.Derived.ContinuousUp.TerminalModulusExtension

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_visible_terminal_modulus_extension
    {p q source map target modulus cert extra modulus' cert' : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
      ContinuousModulusWitness cert extra cert' ->
        Cont modulus extra modulus' ->
          ContinuousFunctionCarrier (append p source) map (append p target)
            (append modulus' q) (append (append p cert') q) := by
  intro carrier terminalWitness modulusRel
  have visibleData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp carrier
  have central :
      ContinuousFunctionCarrier source map target modulus' cert' :=
    ContinuousFunctionCarrier_terminal_modulus_extension visibleData.right.right
      terminalWitness modulusRel
  exact
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus')
      (cert := cert')).mpr
      (And.intro visibleData.left (And.intro visibleData.right.left central))

end BEDC.Derived.ContinuousUp
