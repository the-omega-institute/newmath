import BEDC.Derived.ComplexUp

namespace BEDC.Derived.GammaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

def GammaPoleLocus (s : BHist) : Prop :=
  ∃ n : BHist, UnaryHistory n ∧ hsame s (append (BHist.e1 n) (BHist.e1 BHist.Empty))

def GammaDomainCore (s apart : BHist) : Prop :=
  ComplexHistoryCarrier s ∧ UnaryHistory apart ∧ (GammaPoleLocus s -> False)

theorem GammaPoleLocus_complex_carrier_witness {s : BHist} :
    GammaPoleLocus s ->
      ∃ n : BHist,
        UnaryHistory n ∧ hsame s (append (BHist.e1 n) (BHist.e1 BHist.Empty)) ∧
          ComplexHistoryCarrier s := by
  intro pole
  cases pole with
  | intro n data =>
      cases data with
      | intro nUnary samePole =>
          have realCarrier : RatHistoryCarrier (BHist.e1 n) := by
            exact RatHistoryCarrier_iff_positive_denominator.mpr
              (PositiveUnaryDenominator_e1_iff_unary.mpr nUnary)
          have imagCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
            exact RatHistoryCarrier_iff_positive_denominator.mpr
              (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
          have poleCarrier :
              ComplexHistoryCarrier (append (BHist.e1 n) (BHist.e1 BHist.Empty)) := by
            exact ProdHistoryCarrier_append_intro realCarrier imagCarrier
          exact Exists.intro n
            (And.intro nUnary
              (And.intro samePole
                (ProdHistoryCarrier_hsame_transport (hsame_symm samePole) poleCarrier)))

theorem GammaDomainCore_not_empty {s apart : BHist} :
    GammaDomainCore s apart -> hsame s BHist.Empty -> False := by
  intro domain sameEmpty
  exact ComplexHistoryCarrier_not_empty domain.left sameEmpty

theorem GammaPoleLocus_hsame_transport_witness {s t : BHist} :
    hsame s t ->
      GammaPoleLocus s ->
        GammaPoleLocus t ∧
          ∃ n : BHist, UnaryHistory n ∧
            hsame t (append (BHist.e1 n) (BHist.e1 BHist.Empty)) := by
  intro sameST pole
  cases pole with
  | intro n data =>
      cases data with
      | intro nUnary sameSPole =>
          have sameTPole : hsame t (append (BHist.e1 n) (BHist.e1 BHist.Empty)) :=
            hsame_trans (hsame_symm sameST) sameSPole
          exact And.intro (Exists.intro n (And.intro nUnary sameTPole))
            (Exists.intro n (And.intro nUnary sameTPole))

theorem GammaPoleLocus_witness_unique {s n m : BHist} :
    (UnaryHistory n ∧ hsame s (append (BHist.e1 n) (BHist.e1 BHist.Empty))) ->
      (UnaryHistory m ∧ hsame s (append (BHist.e1 m) (BHist.e1 BHist.Empty))) ->
        hsame n m := by
  intro left right
  have sameAnchors :
      hsame (append (BHist.e1 n) (BHist.e1 BHist.Empty))
        (append (BHist.e1 m) (BHist.e1 BHist.Empty)) :=
    hsame_trans (hsame_symm left.right) right.right
  exact hsame_e1_iff.mp (append_right_cancel (k := BHist.e1 BHist.Empty) sameAnchors)

end BEDC.Derived.GammaUp
