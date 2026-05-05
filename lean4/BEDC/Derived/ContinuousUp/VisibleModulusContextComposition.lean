import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_visible_modulus_context_comp_central_package
    {p q source middle target f g fg modF modG modFG certF certG cert : BHist} :
    ContinuousFunctionCarrier (append p source) f (append p middle) (append modF q)
        (append (append p certF) q) ->
      ContinuousFunctionCarrier (append p middle) g (append p target) (append modG q)
        (append (append p certG) q) ->
        Cont f g fg -> Cont modF modG modFG -> Cont target modFG cert ->
          UnaryHistory p ∧ UnaryHistory q ∧
            ContinuousFunctionCarrier source f middle modF certF ∧
              ContinuousFunctionCarrier middle g target modG certG ∧
                ContinuousFunctionCarrier (append p source) fg (append p target)
                  (append modFG q) (append (append p cert) q) := by
  intro first second fgRel modRel certRel
  have firstData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := f) (target := middle) (modulus := modF)
      (cert := certF)).mp first
  have secondData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := middle) (map := g) (target := target) (modulus := modG)
      (cert := certG)).mp second
  have central :
      ContinuousFunctionCarrier source fg target modFG cert :=
    ContinuousFunctionCarrier_comp_closed firstData.right.right secondData.right.right
      fgRel modRel certRel
  have visible :
      ContinuousFunctionCarrier (append p source) fg (append p target) (append modFG q)
        (append (append p cert) q) :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := fg) (target := target) (modulus := modFG)
      (cert := cert)).mpr
      (And.intro firstData.left (And.intro secondData.right.left central))
  exact And.intro firstData.left
    (And.intro secondData.right.left
      (And.intro firstData.right.right (And.intro secondData.right.right visible)))

end BEDC.Derived.ContinuousUp
