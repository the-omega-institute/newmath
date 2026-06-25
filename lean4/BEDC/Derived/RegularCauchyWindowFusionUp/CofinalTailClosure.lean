import BEDC.Derived.RegularCauchyWindowFusionUp.BudgetMeet

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyWindowFusionCarrier [AskSetup] [PackageSetup]
    (R W S D E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyWindowFusionCofinalTailClosure [AskSetup] [PackageSetup]
    {R W S D E H C P N tailRead budgetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyWindowFusionCarrier R W S D E H C P N bundle pkg →
      Cont W S tailRead →
        Cont D E budgetRead →
          Cont tailRead budgetRead sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                UnaryHistory sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier tailRoute budgetRoute sealRoute sealPkg
  obtain ⟨_rUnary, wUnary, sUnary, dUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, provenancePkg, namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed dUnary eUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary budgetUnary sealRoute
  exact ⟨tailUnary, budgetUnary, sealUnary, provenancePkg, namePkg, sealPkg⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
