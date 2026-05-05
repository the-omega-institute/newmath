import BEDC.Derived.ContinuousUp.EmptyMap
import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_visible_modulus_context_empty_map_exactness
    {p q source target modulus cert : BHist} :
    ContinuousFunctionCarrier (append p source) BHist.Empty (append p target)
        (append modulus q) (append (append p cert) q) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ hsame target source ∧
        ContinuousModulusWitness target modulus cert := by
  constructor
  · intro visible
    have visibleData :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := BHist.Empty) (target := target)
        (modulus := modulus) (cert := cert)).mp visible
    have centralData :=
      (ContinuousFunctionCarrier_empty_map_iff (source := source) (target := target)
        (modulus := modulus) (cert := cert)).mp visibleData.right.right
    exact And.intro visibleData.left (And.intro visibleData.right.left centralData)
  · intro data
    have centralCarrier :
        ContinuousFunctionCarrier source BHist.Empty target modulus cert :=
      (ContinuousFunctionCarrier_empty_map_iff (source := source) (target := target)
        (modulus := modulus) (cert := cert)).mpr
        (And.intro data.right.right.left data.right.right.right)
    exact
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := BHist.Empty) (target := target)
        (modulus := modulus) (cert := cert)).mpr
        (And.intro data.left (And.intro data.right.left centralCarrier))

end BEDC.Derived.ContinuousUp
