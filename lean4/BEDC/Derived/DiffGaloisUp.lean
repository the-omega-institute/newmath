import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffGaloisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffGaloisFaithfulActionLedger_basis_fold_surface
    {seed action actionLedger sourceSurface : BHist} {basisRows : List BHist} :
    UnaryHistory seed -> UnaryHistory action ->
      (forall row : BHist, List.Mem row basisRows -> UnaryHistory row) ->
        Cont (List.foldl append seed basisRows) action actionLedger ->
          Cont seed actionLedger sourceSurface ->
            UnaryHistory (List.foldl append seed basisRows) ∧ UnaryHistory actionLedger ∧
              UnaryHistory sourceSurface ∧
                hsame actionLedger (append (List.foldl append seed basisRows) action) ∧
                  hsame sourceSurface (append seed actionLedger) := by
  intro seedUnary actionUnary basisUnary actionRow sourceRow
  have foldUnary :
      forall {start : BHist} {rows : List BHist},
        UnaryHistory start ->
          (forall row : BHist, List.Mem row rows -> UnaryHistory row) ->
            UnaryHistory (List.foldl append start rows) := by
    intro start rows startUnary rowsUnary
    induction rows generalizing start with
    | nil =>
        exact startUnary
    | cons head tail ih =>
        have headUnary : UnaryHistory head :=
          rowsUnary head (List.Mem.head tail)
        have nextUnary : UnaryHistory (append start head) :=
          unary_append_closed startUnary headUnary
        exact ih nextUnary (by
          intro row rowMem
          exact rowsUnary row (List.Mem.tail head rowMem))
  have basisFoldUnary : UnaryHistory (List.foldl append seed basisRows) :=
    foldUnary seedUnary basisUnary
  have actionLedgerUnary : UnaryHistory actionLedger :=
    unary_cont_closed basisFoldUnary actionUnary actionRow
  have sourceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed seedUnary actionLedgerUnary sourceRow
  exact And.intro basisFoldUnary
    (And.intro actionLedgerUnary
      (And.intro sourceUnary
        (And.intro actionRow sourceRow)))

end BEDC.Derived.DiffGaloisUp
