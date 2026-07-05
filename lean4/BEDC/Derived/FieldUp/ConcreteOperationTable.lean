import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def RatupFieldupConcreteOperationTable : Type :=
  { row : BHist //
    UnaryHistory row ∧
      (RatHistoryCarrier row ∨ RatDenomUnitCarrier row ∨ FieldSingletonCarrier row ∨
        hsame row (append (BHist.e1 BHist.Empty) BHist.Empty)) }

end BEDC.Derived.FieldUp
