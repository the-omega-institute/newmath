import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_uniform_diagonal_consumer_pullback
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n diagRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont u v t →
        Cont t w q →
          Cont q e h →
            Cont h c diagRead →
              Cont diagRead p uniformRead →
                PkgSig bundle uniformRead pkg →
                  UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory t ∧ UnaryHistory w ∧
                    UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧
                      UnaryHistory p ∧ UnaryHistory diagRead ∧ UnaryHistory uniformRead ∧
                        Cont u v t ∧ Cont t w q ∧ Cont q e h ∧ Cont h c diagRead ∧
                          Cont diagRead p uniformRead ∧ PkgSig bundle p pkg ∧
                            PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorRoute windowRoute sealRoute diagRoute uniformRoute uniformPkg
  obtain ⟨_m0Unary, _m1Unary, uUnary, vUnary, _tUnary, wUnary, _qUnary, eUnary, hUnary,
    cUnary, pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩ := carrier
  have tUnary : UnaryHistory t :=
    unary_cont_closed uUnary vUnary selectorRoute
  have qUnary : UnaryHistory q :=
    unary_cont_closed tUnary wUnary windowRoute
  have hUnaryFromRoute : UnaryHistory h :=
    unary_cont_closed qUnary eUnary sealRoute
  have diagUnary : UnaryHistory diagRead :=
    unary_cont_closed hUnary cUnary diagRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed diagUnary pUnary uniformRoute
  exact
    ⟨uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnaryFromRoute, cUnary, pUnary,
      diagUnary, uniformUnary, selectorRoute, windowRoute, sealRoute, diagRoute,
      uniformRoute, pPkg, uniformPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
