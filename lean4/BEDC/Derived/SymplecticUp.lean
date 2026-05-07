import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SymplecticUp

open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SymplecticCarrierClassifierSurface
    (manifold form derivative closed pairing : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧ UnaryHistory form ∧ UnaryHistory derivative ∧
    Cont form derivative closed ∧ Cont manifold form pairing

theorem SymplecticCarrierClassifierSurface_obligations
    {manifold form derivative closed pairing : BHist} :
    SymplecticCarrierClassifierSurface manifold form derivative closed pairing ->
      ManifoldSingletonCarrier manifold ∧ UnaryHistory manifold ∧ UnaryHistory form ∧
        UnaryHistory derivative ∧ UnaryHistory closed ∧ UnaryHistory pairing ∧
          Cont form derivative closed ∧ Cont manifold form pairing := by
  intro surface
  have manifoldRows := ManifoldSingletonCarrier_topology_scope surface.left
  have closedUnary : UnaryHistory closed :=
    unary_cont_closed surface.right.left surface.right.right.left surface.right.right.right.left
  have pairingUnary : UnaryHistory pairing :=
    unary_cont_closed manifoldRows.right.left surface.right.left surface.right.right.right.right
  have formUnary : UnaryHistory form := surface.right.left
  have derivativeUnary : UnaryHistory derivative := surface.right.right.left
  have closedRow : Cont form derivative closed := surface.right.right.right.left
  have pairingRow : Cont manifold form pairing := surface.right.right.right.right
  exact And.intro surface.left
    (And.intro manifoldRows.right.left
      (And.intro formUnary
        (And.intro derivativeUnary
          (And.intro closedUnary
            (And.intro pairingUnary
              (And.intro closedRow pairingRow))))))

end BEDC.Derived.SymplecticUp
