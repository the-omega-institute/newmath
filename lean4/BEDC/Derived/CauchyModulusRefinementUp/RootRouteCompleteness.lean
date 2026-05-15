import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_route_completeness [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h endpoint ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                  UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                    UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                      UnaryHistory selected ∧ UnaryHistory readback ∧
                        UnaryHistory sealRead ∧ UnaryHistory endpoint ∧ Cont m0 m1 u ∧
                          Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
                            Cont t w selected ∧ Cont selected q readback ∧
                              Cont readback e sealRead ∧ Cont sealRead h endpoint ∧
                                PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier selectedRoute readbackRoute sealReadRoute endpointRoute endpointPkg
  have m0Unary : UnaryHistory m0 := carrier.left
  have m1Unary : UnaryHistory m1 := carrier.right.left
  have uUnary : UnaryHistory u := carrier.right.right.left
  have vUnary : UnaryHistory v := carrier.right.right.right.left
  have tUnary : UnaryHistory t := carrier.right.right.right.right.left
  have wUnary : UnaryHistory w := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory q := carrier.right.right.right.right.right.right.left
  have eUnary : UnaryHistory e := carrier.right.right.right.right.right.right.right.left
  have hUnary : UnaryHistory h := carrier.right.right.right.right.right.right.right.right.left
  have cUnary : UnaryHistory c :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have pUnary : UnaryHistory p :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory n :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have m0m1u : Cont m0 m1 u :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have uvt : Cont u v t :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have twq : Cont t w q :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have qeh : Cont q e h :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have hn : hsame h n :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealReadRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealReadUnary hUnary endpointRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, selectedUnary, readbackUnary, sealReadUnary, endpointUnary, m0m1u,
      uvt, twq, qeh, selectedRoute, readbackRoute, sealReadRoute, endpointRoute, pPkg,
      endpointPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
