import BEDC.Derived.RegularCauchyProductBudgetUp.Obligations

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_source_coverage [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB dyadicA dyadicB readback
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg ->
      Cont A WA windowA ->
        Cont B WB windowB ->
          Cont windowA DA dyadicA ->
            Cont windowB DB dyadicB ->
              Cont DA DB D ->
                Cont D E readback ->
                  Cont readback S sealRead ->
                    PkgSig bundle dyadicA pkg ->
                      PkgSig bundle dyadicB pkg ->
                        PkgSig bundle E pkg ->
                          PkgSig bundle readback pkg ->
                            PkgSig bundle sealRead pkg ->
                              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧
                                UnaryHistory WB ∧ UnaryHistory DA ∧ UnaryHistory DB ∧
                                  UnaryHistory D ∧ UnaryHistory E ∧
                                    UnaryHistory readback ∧ UnaryHistory sealRead ∧
                                      Cont A WA windowA ∧ Cont B WB windowB ∧
                                        Cont windowA DA dyadicA ∧
                                          Cont windowB DB dyadicB ∧ Cont DA DB D ∧
                                            Cont D E readback ∧
                                              Cont readback S sealRead ∧
                                                PkgSig bundle E pkg ∧
                                                  PkgSig bundle readback pkg ∧
                                                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowARoute windowBRoute dyadicARoute dyadicBRoute productRoute
    readbackRoute sealRoute _dyadicAPkg _dyadicBPkg ledgerPkg readbackPkg sealPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, dUnary, eUnary,
    _rUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    _namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed dUnary eUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sUnary sealRoute
  exact
    ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, dUnary, eUnary,
      readbackUnary, sealUnary, windowARoute, windowBRoute, dyadicARoute,
      dyadicBRoute, productRoute, readbackRoute, sealRoute, ledgerPkg, readbackPkg,
      sealPkg⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
