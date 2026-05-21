import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_primitive_scope [AskSetup] [PackageSetup]
    {q s g d r w h c p n preservationRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont g d preservationRead →
        Cont preservationRead r consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
              UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧
                UnaryHistory p ∧ UnaryHistory n ∧ UnaryHistory preservationRead ∧
                  UnaryHistory consumer ∧ Cont q s g ∧ Cont g d r ∧ Cont w h c ∧
                    Cont g d preservationRead ∧ Cont preservationRead r consumer ∧
                      PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier preservationRoute consumerRoute consumerPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary, pUnary,
    nUnary, qsRoute, gdRoute, whRoute, pPkg⟩ := carrier
  have preservationUnary : UnaryHistory preservationRead :=
    unary_cont_closed gUnary dUnary preservationRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed preservationUnary rUnary consumerRoute
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary, pUnary,
      nUnary, preservationUnary, consumerUnary, qsRoute, gdRoute, whRoute,
      preservationRoute, consumerRoute, pPkg, consumerPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
