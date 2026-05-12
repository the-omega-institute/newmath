import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ConvRadCheckedRowReduct_coefficient_tail_public_boundary
    {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadCheckedRowReduct a z0 R ->
      ConvRadCheckedRowReduct (fun n : Nat => a (Nat.succ n)) z0 R ∧
        ConvRad (fun n : Nat => a (Nat.succ n)) R ∧ UnaryHistory R := by
  intro checked
  obtain ⟨source, readback⟩ := checked
  obtain ⟨carrier, radius⟩ := source
  obtain ⟨K, witnessAt⟩ := readback
  have tailCarrier : PowerSeriesCarrier (fun n : Nat => a (Nat.succ n)) z0 :=
    ⟨carrier.left, (fun n : Nat => carrier.right.left (Nat.succ n)), carrier.right.right⟩
  have tailRadius : ConvRad (fun n : Nat => a (Nat.succ n)) R :=
    ConvRad_successor_coefficients_closed radius
  have tailReadback :
      ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
        PowerSeriesCarrier (fun n : Nat => a (Nat.succ n)) z0 ∧
          GeomBound (fun n : Nat => a (Nat.succ n)) r (K r) ∧ UnaryHistory R := by
    exact Exists.intro K (by
      intro r radiusUnary continuation
      have sourceRow := witnessAt radiusUnary continuation
      have tailBound : GeomBound (fun n : Nat => a (Nat.succ n)) r (K r) :=
        ⟨sourceRow.right.left.left,
          sourceRow.right.left.right.left,
          fun n : Nat => sourceRow.right.left.right.right (Nat.succ n)⟩
      exact ⟨tailCarrier, tailBound, sourceRow.right.right⟩)
  exact
    ⟨⟨⟨tailCarrier, tailRadius⟩, tailReadback⟩, tailRadius, radius.left⟩

end BEDC.Derived.ConvergenceRadiusUp
