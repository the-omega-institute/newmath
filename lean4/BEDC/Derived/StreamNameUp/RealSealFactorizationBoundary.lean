import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamnameRealSealFactorizationBoundary
    {s t : BHist -> BHist} {window : ProbeBundle BHist} {n ledger sealRow : BHist} :
    RatStreamNameFiniteWindowClassifier s t window ->
      InBundle n window ->
        UnaryHistory n ->
          Cont (s n) (t n) ledger ->
            Cont ledger n sealRow ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
                  (fun row : BHist => hsame row sealRow)
                  (fun row : BHist => hsame row sealRow ∧ Cont ledger n sealRow)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont SemanticNameCert hsame
  intro finiteWindow member nUnary ledgerRoute sealRoute
  have selected : RatHistoryClassifier (s n) (t n) :=
    finiteWindow n member nUnary
  have sourceUnary : UnaryHistory (s n) :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp selected.left)).left
  have targetUnary : UnaryHistory (t n) :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp selected.right.left)).left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary targetUnary ledgerRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary nUnary sealRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow ⟨hsame_refl sealRow, sealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealRoute⟩
  }

end BEDC.Derived.StreamNameUp
