import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_open_phase_window_selector_lock [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance nameRow
      selectorWindow selectorSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont request windows selectorWindow →
        Cont selectorWindow selector selectorSeal →
          PkgSig bundle selectorSeal pkg →
            UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory selector ∧
              UnaryHistory selectorWindow ∧ UnaryHistory selectorSeal ∧
                Cont request windows selectorWindow ∧
                  Cont selectorWindow selector selectorSeal ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle selectorSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier requestWindowsSelectorWindow selectorWindowSelectorSeal selectorSealPkg
  have selectorWindowUnary : UnaryHistory selectorWindow :=
    unary_cont_closed carrier.request_unary carrier.windows_unary requestWindowsSelectorWindow
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorWindowUnary carrier.selector_unary selectorWindowSelectorSeal
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.selector_unary,
      selectorWindowUnary, selectorSealUnary, requestWindowsSelectorWindow,
      selectorWindowSelectorSeal, carrier.provenance_pkg, selectorSealPkg⟩

end BEDC.Derived.RealWindowBudgetUp
