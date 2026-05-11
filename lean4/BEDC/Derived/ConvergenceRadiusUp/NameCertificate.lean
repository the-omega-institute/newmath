import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem conv_rad_name_certificate :
    NameCert (fun R : BHist => exists a : Nat -> BHist, ConvRad a R) hsame := by
  let coefficient : BHist := append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
  let constantFamily : Nat -> BHist := fun _n : Nat => coefficient
  have denominatorCarrier : RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    Iff.mpr RatUp.RatHistoryCarrier_iff_positive_denominator
      (Iff.mpr RatUp.PositiveUnaryDenominator_e1_iff_unary unary_empty)
  have coefficientCarrier : ComplexHistoryCarrier coefficient :=
    Exists.intro (BHist.e1 BHist.Empty)
      (Exists.intro (BHist.e1 BHist.Empty)
        (And.intro denominatorCarrier
          (And.intro denominatorCarrier (cont_intro rfl))))
  have radius : ConvRad constantFamily (BHist.e1 BHist.Empty) := by
    exact And.intro (unary_e1_closed unary_empty)
      (Exists.intro (fun _r : BHist => BHist.Empty)
        (fun {r : BHist} rUnary _continuation =>
          And.intro rUnary
            (And.intro unary_empty
              (fun _n : Nat => coefficientCarrier))))
  exact {
    carrier_inhabited :=
      Exists.intro (BHist.e1 BHist.Empty)
        (Exists.intro constantFamily radius)
    equiv_refl := by
      intro R _source
      exact hsame_refl R
    equiv_symm := by
      intro R R' same
      exact hsame_symm same
    equiv_trans := by
      intro R R' R'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro R R' same source
      cases source with
      | intro a radiusR =>
          exact Exists.intro a
            (ConvRad_radius_transport same radiusR (unary_transport radiusR.left same))
  }

end BEDC.Derived.ConvergenceRadiusUp
