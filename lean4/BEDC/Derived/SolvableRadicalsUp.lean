import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SolvableRadicalsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem SolvableRadicalsTowerStepLedger_assoc_surface
    {base towerStep radicand radicalStep splitting topField towerSurface : BHist} :
    UnaryHistory base -> UnaryHistory towerStep -> UnaryHistory radicand ->
      UnaryHistory splitting -> Cont base towerStep radicalStep ->
        Cont radicalStep radicand topField -> Cont topField splitting towerSurface ->
          ∃ adjacentRow : BHist,
            Cont towerStep radicand adjacentRow ∧ Cont base adjacentRow topField ∧
              Cont topField splitting towerSurface ∧ UnaryHistory radicalStep ∧
                UnaryHistory adjacentRow ∧ UnaryHistory topField ∧
                  UnaryHistory towerSurface ∧ hsame radicalStep (append base towerStep) ∧
                    hsame adjacentRow (append towerStep radicand) ∧
                      hsame topField (append radicalStep radicand) ∧
                        hsame towerSurface (append topField splitting) := by
  intro baseUnary towerUnary radicandUnary splittingUnary radicalRow topFieldRow surfaceRow
  have radicalUnary : UnaryHistory radicalStep :=
    unary_cont_closed baseUnary towerUnary radicalRow
  have topUnary : UnaryHistory topField :=
    unary_cont_closed radicalUnary radicandUnary topFieldRow
  have surfaceUnary : UnaryHistory towerSurface :=
    unary_cont_closed topUnary splittingUnary surfaceRow
  cases cont_assoc_left_exists radicalRow topFieldRow with
  | intro adjacentRow adjacentData =>
      have adjacentUnary : UnaryHistory adjacentRow :=
        unary_cont_closed towerUnary radicandUnary adjacentData.left
      exact Exists.intro adjacentRow
        (And.intro adjacentData.left
          (And.intro adjacentData.right
            (And.intro surfaceRow
              (And.intro radicalUnary
                (And.intro adjacentUnary
                  (And.intro topUnary
                    (And.intro surfaceUnary
                      (And.intro radicalRow
                        (And.intro adjacentData.left
                          (And.intro topFieldRow surfaceRow))))))))))

end BEDC.Derived.SolvableRadicalsUp
