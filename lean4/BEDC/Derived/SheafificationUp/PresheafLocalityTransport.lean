import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPresheafLocalityTransport [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N presheafRead transportedLocality : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P H presheafRead →
        Cont presheafRead L transportedLocality →
          PkgSig bundle transportedLocality pkg →
            UnaryHistory P ∧ UnaryHistory H ∧ UnaryHistory L ∧
              UnaryHistory presheafRead ∧ UnaryHistory transportedLocality ∧
                Cont P H presheafRead ∧ Cont presheafRead L transportedLocality ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle transportedLocality pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier presheafRoute localityRoute transportedPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, _gUnary, _sUnary, hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, namePkg⟩ := carrier
  have presheafReadUnary : UnaryHistory presheafRead :=
    unary_cont_closed pUnary hUnary presheafRoute
  have transportedUnary : UnaryHistory transportedLocality :=
    unary_cont_closed presheafReadUnary lUnary localityRoute
  exact
    ⟨pUnary, hUnary, lUnary, presheafReadUnary, transportedUnary, presheafRoute,
      localityRoute, namePkg, transportedPkg⟩

end BEDC.Derived.SheafificationUp
