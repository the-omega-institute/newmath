import BEDC.Derived.RegularCauchyProductBudgetUp.Obligations

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_bilinear_window [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB dyadicA dyadicB readback «seal» :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg ->
      Cont A WA windowA ->
        Cont B WB windowB ->
          Cont windowA DA dyadicA ->
            Cont windowB DB dyadicB ->
              Cont DA DB D ->
                Cont D E readback ->
                  Cont readback S «seal» ->
                    PkgSig bundle dyadicA pkg ->
                      PkgSig bundle dyadicB pkg ->
                        PkgSig bundle readback pkg ->
                          PkgSig bundle «seal» pkg ->
                            UnaryHistory windowA ∧ UnaryHistory windowB ∧
                              UnaryHistory dyadicA ∧ UnaryHistory dyadicB ∧
                                UnaryHistory D ∧ UnaryHistory E ∧
                                  UnaryHistory readback ∧ UnaryHistory «seal» ∧
                                    Cont A WA windowA ∧ Cont B WB windowB ∧
                                      Cont windowA DA dyadicA ∧
                                        Cont windowB DB dyadicB ∧ Cont DA DB D ∧
                                          Cont D E readback ∧ Cont readback S «seal» ∧
                                            PkgSig bundle N pkg ∧
                                              PkgSig bundle readback pkg ∧
                                                PkgSig bundle «seal» pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowARoute windowBRoute dyadicARoute dyadicBRoute productRoute
    readbackRoute sealRoute _dyadicAPkg _dyadicBPkg readbackPkg sealPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, dUnary, eUnary,
    _rUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed aUnary waUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed bUnary wbUnary windowBRoute
  have dyadicAUnary : UnaryHistory dyadicA :=
    unary_cont_closed windowAUnary daUnary dyadicARoute
  have dyadicBUnary : UnaryHistory dyadicB :=
    unary_cont_closed windowBUnary dbUnary dyadicBRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed dUnary eUnary readbackRoute
  have sealedUnary : UnaryHistory «seal» :=
    unary_cont_closed readbackUnary sUnary sealRoute
  exact
    ⟨windowAUnary, windowBUnary, dyadicAUnary, dyadicBUnary, dUnary, eUnary,
      readbackUnary, sealedUnary, windowARoute, windowBRoute, dyadicARoute, dyadicBRoute,
      productRoute, readbackRoute, sealRoute, namePkg, readbackPkg, sealPkg⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
