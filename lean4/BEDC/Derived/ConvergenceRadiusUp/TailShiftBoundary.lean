import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ConvRad_tail_shift_checked_row_reduct_semantic_boundary
    {a : Nat -> BHist} {z0 R tailEndpoint : BHist} :
    ConvRadCheckedRowReduct a z0 R ->
      Cont R z0 tailEndpoint ->
        ConvRadCheckedRowReduct (fun n : Nat => a (Nat.succ n)) z0 R ∧
          UnaryHistory tailEndpoint ∧ hsame tailEndpoint (append R z0) ∧
            SemanticNameCert (ConvRad (fun n : Nat => a (Nat.succ n)))
              (ConvRad (fun n : Nat => a (Nat.succ n)))
              (ConvRad (fun n : Nat => a (Nat.succ n))) hsame := by
  intro checked endpointRow
  have tailRadius : UnaryHistory R ∧ ConvRad (fun n : Nat => a (Nat.succ n)) R :=
    ConvRad_coefficient_tail_closed checked.left.right
  have tailCarrier : PowerSeriesCarrier (fun n : Nat => a (Nat.succ n)) z0 :=
    And.intro checked.left.left.left
      (And.intro
        (fun n : Nat => checked.left.left.right.left (Nat.succ n))
        checked.left.left.right.right)
  have tailSource : ConvRadSourceSpec (fun n : Nat => a (Nat.succ n)) z0 R :=
    And.intro tailCarrier tailRadius.right
  have tailChecked : ConvRadCheckedRowReduct (fun n : Nat => a (Nat.succ n)) z0 R :=
    And.intro tailSource (ConvRadSourceSpec_powerSeries_geomBound_readback tailSource)
  have endpointUnary : UnaryHistory tailEndpoint :=
    unary_cont_closed tailRadius.left checked.left.left.left endpointRow
  exact
    ⟨tailChecked, endpointUnary, endpointRow,
      ConvRad_semanticNameCert tailRadius.right⟩

end BEDC.Derived.ConvergenceRadiusUp
