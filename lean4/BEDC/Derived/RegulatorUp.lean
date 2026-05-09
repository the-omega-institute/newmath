import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive RegulatorLedgerSpine : List BHist -> BHist -> Prop where
  | nil {endpoint : BHist} : UnaryHistory endpoint -> RegulatorLedgerSpine [] endpoint
  | cons {row tail endpoint : BHist} {rest : List BHist} :
      UnaryHistory row -> RegulatorLedgerSpine rest tail -> Cont row tail endpoint ->
        RegulatorLedgerSpine (row :: rest) endpoint

theorem RegulatorLedgerSpine_rows_unary
    {rows : List BHist} {endpoint row : BHist} :
    RegulatorLedgerSpine rows endpoint -> List.Mem row rows -> UnaryHistory row := by
  intro spine rowMem
  induction spine with
  | nil _ =>
      cases rowMem
  | cons rowUnary _ _ ih =>
      cases rowMem with
      | head =>
          exact rowUnary
      | tail _ restMem =>
          exact ih restMem

end BEDC.Derived.RegulatorUp
