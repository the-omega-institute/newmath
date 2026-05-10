import BEDC.Derived.BilinFormUp
import BEDC.Derived.ModuleUp

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ModuleUp

theorem BilinFormBHistObligationSurface_zero_left_pairing_vanishing_row
    {left right scalar additive endpoint scalarLedger ledger scalarZero : BHist}
    (scalarAdd : BHist -> BHist -> BHist) :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame left BHist.Empty -> hsame scalarZero BHist.Empty ->
        hsame (scalarAdd endpoint BHist.Empty) endpoint ->
          (forall {a b c : BHist}, hsame (scalarAdd a b) (scalarAdd a c) -> hsame b c) ->
            hsame endpoint (scalarAdd endpoint endpoint) ->
              hsame endpoint scalarZero ∧ UnaryHistory endpoint ∧
                hsame scalarLedger (append endpoint scalar) ∧ Cont left right endpoint := by
  intro surface leftEmpty scalarZeroEmpty scalarRightZero scalarLeftCancel endpointDuplicate
  have endpointEmpty : hsame endpoint BHist.Empty :=
    ModuleAdditive_duplicate_cancel_empty scalarRightZero scalarLeftCancel endpointDuplicate
  have sameScalarZero : hsame endpoint scalarZero :=
    hsame_trans endpointEmpty (hsame_symm scalarZeroEmpty)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.right.left
  have scalarLedgerReadback : hsame scalarLedger (append endpoint scalar) :=
    surface.right.right.right.right.right.left
  exact And.intro sameScalarZero
    (And.intro endpointUnary
      (And.intro scalarLedgerReadback surface.right.right.right.right.left))

end BEDC.Derived.BilinFormUp
