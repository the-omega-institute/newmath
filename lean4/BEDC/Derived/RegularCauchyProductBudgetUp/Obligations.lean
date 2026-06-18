import BEDC.Derived.RegularCauchyProductBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyProductBudgetCarrier [AskSetup] [PackageSetup]
    (A B WA WB DA DB D E R S H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧ UnaryHistory WB ∧
    UnaryHistory DA ∧ UnaryHistory DB ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyProductBudgetCarrier_window_admission [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB dyadicA dyadicB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg →
      Cont A WA windowA →
        Cont B WB windowB →
          Cont windowA DA dyadicA →
            Cont windowB DB dyadicB →
              PkgSig bundle dyadicA pkg →
                PkgSig bundle dyadicB pkg →
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧
                    UnaryHistory WB ∧ UnaryHistory windowA ∧ UnaryHistory windowB ∧
                      UnaryHistory dyadicA ∧ UnaryHistory dyadicB ∧
                        Cont A WA windowA ∧ Cont B WB windowB ∧
                          Cont windowA DA dyadicA ∧ Cont windowB DB dyadicB ∧
                            PkgSig bundle N pkg ∧ PkgSig bundle dyadicA pkg ∧
                              PkgSig bundle dyadicB pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowARoute windowBRoute dyadicARoute dyadicBRoute dyadicAPkg
    dyadicBPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, _dUnary, _eUnary,
    _rUnary, _sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed aUnary waUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed bUnary wbUnary windowBRoute
  have dyadicAUnary : UnaryHistory dyadicA :=
    unary_cont_closed windowAUnary daUnary dyadicARoute
  have dyadicBUnary : UnaryHistory dyadicB :=
    unary_cont_closed windowBUnary dbUnary dyadicBRoute
  exact
    ⟨aUnary, bUnary, waUnary, wbUnary, windowAUnary, windowBUnary, dyadicAUnary,
      dyadicBUnary, windowARoute, windowBRoute, dyadicARoute, dyadicBRoute, namePkg,
      dyadicAPkg, dyadicBPkg⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
