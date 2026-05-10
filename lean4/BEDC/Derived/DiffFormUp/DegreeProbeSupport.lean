import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormDegreeProbeSupport_wedge_compatibility
    {d e out probe tensor scalar antisym ledger : BHist} {left right : ProbeBundle BHist} :
    DegreeProbeAligned d left -> DegreeProbeAligned e right -> Cont d e out ->
      InBundle probe (bundleAppend left right) -> UnaryHistory probe -> Cont out probe tensor ->
        UnaryHistory antisym -> Cont tensor antisym scalar ->
          hsame ledger (append out (append probe (append tensor (append scalar antisym)))) ->
            DegreeProbeAligned out (bundleAppend left right) ∧ UnaryHistory out ∧
              InBundle probe (bundleAppend left right) ∧ UnaryHistory tensor ∧
                UnaryHistory scalar ∧
                  hsame ledger (append out (append probe (append tensor (append scalar antisym)))) :=
  by
    intro leftAligned rightAligned degreeRoute probeIn probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
    have alignedOut :
        DegreeProbeAligned out (bundleAppend left right) :=
      DiffFormDegreeProbeAligned_bundleAppend_cont leftAligned rightAligned degreeRoute
    have supportRows :
        UnaryHistory out ∧ InBundle probe (bundleAppend left right) ∧ UnaryHistory tensor ∧
          UnaryHistory scalar ∧
            hsame ledger (append out (append probe (append tensor (append scalar antisym)))) :=
      DiffFormDegreeProbeSupport_carrier_admissibility alignedOut probeIn probeUnary tensorRoute
        antisymUnary scalarRoute ledgerRoute
    exact And.intro alignedOut supportRows

end BEDC.Derived.DiffFormUp
