import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContactUp

open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ContactCarrierClassifierSurface (manifold form derivative wedge top : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧ UnaryHistory form ∧ UnaryHistory derivative ∧
    Cont form derivative wedge ∧ Cont wedge BHist.Empty top

theorem ContactCarrierClassifierSurface_form_row_obligation
    {manifold form derivative wedge top : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      ManifoldSingletonCarrier manifold ∧ UnaryHistory manifold ∧ UnaryHistory form ∧
        UnaryHistory derivative ∧ UnaryHistory wedge ∧ UnaryHistory top ∧
          Cont form derivative wedge ∧ Cont wedge BHist.Empty top := by
  intro surface
  have manifoldRows := ManifoldSingletonCarrier_topology_scope surface.left
  have wedgeUnary : UnaryHistory wedge :=
    unary_cont_closed surface.right.left surface.right.right.left surface.right.right.right.left
  have topUnary : UnaryHistory top :=
    unary_cont_closed wedgeUnary unary_empty surface.right.right.right.right
  exact And.intro surface.left
    (And.intro manifoldRows.right.left
      (And.intro surface.right.left
          (And.intro surface.right.right.left
            (And.intro wedgeUnary
              (And.intro topUnary
                (And.intro surface.right.right.right.left surface.right.right.right.right))))))

end BEDC.Derived.ContactUp
