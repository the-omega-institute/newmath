import BEDC.Derived.RegularCauchyProductBudgetUp.Obligations

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudgetCarrier_symmetric_source_window_inversion
    [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg →
      Cont A WA windowA →
        Cont B WB windowB →
          Cont DA DB D →
            Cont D E productRead →
              PkgSig bundle productRead pkg →
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧
                  UnaryHistory WB ∧ UnaryHistory windowA ∧ UnaryHistory windowB ∧
                    UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory productRead ∧
                      Cont A WA windowA ∧ Cont B WB windowB ∧ Cont DA DB D ∧
                        Cont D E productRead ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle productRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowARoute windowBRoute productRoute productReadRoute productReadPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, _daUnary, _dbUnary, dUnary, eUnary,
    _rUnary, _sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed aUnary waUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed bUnary wbUnary windowBRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed dUnary eUnary productReadRoute
  exact
    ⟨aUnary, bUnary, waUnary, wbUnary, windowAUnary, windowBUnary, dUnary, eUnary,
      productReadUnary, windowARoute, windowBRoute, productRoute, productReadRoute,
      namePkg, productReadPkg⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
