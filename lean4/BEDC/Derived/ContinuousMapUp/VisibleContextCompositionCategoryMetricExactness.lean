import BEDC.Derived.CategoryUp.Prefix
import BEDC.Derived.ContinuousMapUp.CategoryMetricDecomposition

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_visible_context_composition_category_metric_exactness
    {p q source middle target f g fg modF modG modFG certF certG cert distF distG
      displayed : BHist} :
    ContinuousMapCarrier (append p source) f (append p middle) modF (append p certF) distF ->
      ContinuousMapCarrier (append p middle) g (append p target) modG (append p certG) distG ->
        Cont f g fg -> Cont modF modG modFG -> Cont target modFG cert ->
          UnaryHistory p ∧ CategoryHomCarrier source target fg ∧
            ContinuousModulusWitness target modFG cert ∧
              MetricDistanceWitness source target (append source target) ∧
                (ContinuousMapCarrier (append p source) fg (append p target) modFG
                    (append p cert) displayed ↔
                  hsame displayed (append (append p source) (append p target))) := by
  intro first second graphRel modulusRel certRel
  have prefixCarrier : UnaryHistory p :=
    unary_append_left_factor first.left.left
  have baseFirst :
      ContinuousMapCarrier source f middle modF certF (append source middle) := by
    have decomposed := ContinuousMapCarrier_category_metric_decomposition.mp first
    have homCarrier : CategoryHomCarrier source middle f :=
      (CategoryHomCarrier_unary_prefix_iff (p := p) (a := source) (b := middle) (f := f)).mp
        decomposed.left |>.right
    have modulusWitness : ContinuousModulusWitness middle modF certF := by
      exact
        (ContinuousModulusWitness_prefix_iff (p := p) (source := middle) (modulus := modF)
          (target := certF)).mp decomposed.right.left |>.right
    exact
      ContinuousMapCarrier_categorical_canonical_distance_exactness.mpr
        ⟨homCarrier, modulusWitness, hsame_refl (append source middle)⟩
  have baseSecond :
      ContinuousMapCarrier middle g target modG certG (append middle target) := by
    have decomposed := ContinuousMapCarrier_category_metric_decomposition.mp second
    have homCarrier : CategoryHomCarrier middle target g :=
      (CategoryHomCarrier_unary_prefix_iff (p := p) (a := middle) (b := target) (f := g)).mp
        decomposed.left |>.right
    have modulusWitness : ContinuousModulusWitness target modG certG := by
      exact
        (ContinuousModulusWitness_prefix_iff (p := p) (source := target) (modulus := modG)
          (target := certG)).mp decomposed.right.left |>.right
    exact
      ContinuousMapCarrier_categorical_canonical_distance_exactness.mpr
        ⟨homCarrier, modulusWitness, hsame_refl (append middle target)⟩
  have composite :
      ContinuousMapCarrier source fg target modFG cert (append source target) :=
    ContinuousMapCarrier_comp_closed baseFirst baseSecond graphRel modulusRel certRel
  have decomposedComposite :=
    ContinuousMapCarrier_category_metric_decomposition.mp composite
  exact
    ⟨prefixCarrier, decomposedComposite.left, decomposedComposite.right.left,
      decomposedComposite.right.right.left,
      ContinuousMapCarrier_prefix_canonical_distance_exactness prefixCarrier composite⟩

end BEDC.Derived.ContinuousMapUp
