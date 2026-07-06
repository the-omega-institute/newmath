import BEDC.Derived.AuditMapRouteBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapRouteBudgetUp

open BEDC.Derived.AuditMapRouteBudgetUp.TasteGate
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AuditMapRouteBudgetCarrier [AskSetup] [PackageSetup]
    (E S R G Q L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  ∃ token : AuditMapRouteBudgetUp,
    token = AuditMapRouteBudgetUp.mk E S R G Q L H C P N ∧
      UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory G ∧
        UnaryHistory Q ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle N pkg

theorem AuditMapRouteBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {E S R G Q L H C P N routeRead gateRead reportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapRouteBudgetCarrier E S R G Q L H C P N bundle pkg →
      Cont E S routeRead →
        Cont G Q gateRead →
          Cont routeRead L reportRead →
            PkgSig bundle N pkg →
              PkgSig bundle reportRead pkg →
                UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory G ∧
                  UnaryHistory Q ∧ UnaryHistory L ∧ UnaryHistory routeRead ∧
                    UnaryHistory gateRead ∧ UnaryHistory reportRead ∧
                      Cont E S routeRead ∧ Cont G Q gateRead ∧
                        Cont routeRead L reportRead ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle reportRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier routeRoute gateRoute reportRoute namePkg reportPkg
  obtain ⟨_token, _tokenEq, eUnary, sUnary, rUnary, gUnary, qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed eUnary sUnary routeRoute
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed gUnary qUnary gateRoute
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed routeUnary lUnary reportRoute
  exact
    ⟨eUnary, sUnary, rUnary, gUnary, qUnary, lUnary, routeUnary, gateUnary,
      reportUnary, routeRoute, gateRoute, reportRoute, namePkg, reportPkg⟩

theorem AuditMapRouteBudgetCarrier_falsifiable_boundary [AskSetup] [PackageSetup]
    {E S R G Q L H C P N routeRead gateRead reportRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapRouteBudgetCarrier E S R G Q L H C P N bundle pkg ->
      Cont E S routeRead ->
        Cont G Q gateRead ->
          Cont L H refusalRead ->
            PkgSig bundle reportRead pkg ->
              PkgSig bundle refusalRead pkg ->
                UnaryHistory G ∧ UnaryHistory L ∧ UnaryHistory gateRead ∧
                  UnaryHistory refusalRead ∧ Cont G Q gateRead ∧
                    Cont L H refusalRead ∧ PkgSig bundle reportRead pkg ∧
                      PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier _routeRoute gateRoute refusalRoute reportPkg refusalPkg
  obtain ⟨_token, _tokenEq, _eUnary, _sUnary, _rUnary, gUnary, qUnary, lUnary,
    hUnary, _cUnary, _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed gUnary qUnary gateRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed lUnary hUnary refusalRoute
  exact
    ⟨gUnary, lUnary, gateUnary, refusalUnary, gateRoute, refusalRoute, reportPkg,
      refusalPkg⟩

end BEDC.Derived.AuditMapRouteBudgetUp
