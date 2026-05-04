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

theorem GammaPoleLocus_not_empty {s : BHist} :
    GammaPoleLocus s -> hsame s BHist.Empty -> False := by
  intro pole sameEmpty
  cases GammaPoleLocus_complex_carrier_witness pole with
  | intro _n data =>
      exact ComplexHistoryCarrier_not_empty data.right.right sameEmpty

theorem GammaPoleLocus_append_unary_complex_carrier {s q : BHist} :
    GammaPoleLocus s -> UnaryHistory q ->
      ComplexHistoryCarrier (append s q) ∧ (hsame (append s q) BHist.Empty -> False) := by
  intro pole qUnary
  cases GammaPoleLocus_complex_carrier_witness pole with
  | intro _n data =>
      have appendCarrier : ComplexHistoryCarrier (append s q) :=
        ComplexHistoryCarrier_append_unary_closed data.right.right qUnary
      exact And.intro appendCarrier (ComplexHistoryCarrier_not_empty appendCarrier)

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

theorem GammaDomainCore_hsame_transport_exclusions {s t apart : BHist} :
    hsame s t -> GammaDomainCore s apart ->
      (GammaPoleLocus t -> False) ∧ (hsame t BHist.Empty -> False) := by
  intro sameST domain
  constructor
  · intro poleT
    have transported := GammaPoleLocus_hsame_transport_witness (hsame_symm sameST) poleT
    exact domain.right.right transported.left
  · intro sameEmptyT
    exact GammaDomainCore_not_empty domain (hsame_trans sameST sameEmptyT)

theorem GammaDomainCore_hsame_transport {s t apart : BHist} :
    hsame s t -> GammaDomainCore s apart ->
      GammaDomainCore t apart ∧ (hsame t BHist.Empty -> False) := by
  intro sameST domain
  have exclusions := GammaDomainCore_hsame_transport_exclusions sameST domain
  constructor
  · exact And.intro (ProdHistoryCarrier_hsame_transport sameST domain.left)
      (And.intro domain.right.left exclusions.left)
  · exact exclusions.right

theorem GammaDomainCore_hsame_transport_not_empty {s t apart : BHist} :
    hsame s t -> GammaDomainCore s apart ->
      GammaDomainCore t apart ∧ (hsame t BHist.Empty -> False) := by
  intro sameST domain
  have carrierT : ComplexHistoryCarrier t :=
    ProdHistoryCarrier_hsame_transport sameST domain.left
  have noPoleT : GammaPoleLocus t -> False := by
    intro poleT
    have transported :=
      GammaPoleLocus_hsame_transport_witness (hsame_symm sameST) poleT
    exact domain.right.right transported.left
  have domainT : GammaDomainCore t apart :=
    And.intro carrierT (And.intro domain.right.left noPoleT)
  exact And.intro domainT (GammaDomainCore_not_empty domainT)

end BEDC.Derived.GammaUp
