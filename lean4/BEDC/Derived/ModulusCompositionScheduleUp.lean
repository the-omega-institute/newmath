import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusCompositionScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusCompositionScheduleRealHandoff [AskSetup] [PackageSetup]
    {mu nu Wmu Wnu eps delta R A E H C P N outerRead innerRead arithmeticRead
      readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory mu ∧ UnaryHistory nu ∧ UnaryHistory Wmu ∧ UnaryHistory Wnu ∧
      UnaryHistory eps ∧ UnaryHistory delta ∧ UnaryHistory R ∧ UnaryHistory A ∧
        UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
          UnaryHistory N ∧ PkgSig bundle P pkg) →
      Cont eps mu outerRead →
        Cont outerRead delta innerRead →
          Cont innerRead A arithmeticRead →
            Cont arithmeticRead R readbackRead →
              Cont readbackRead E sealRead →
                PkgSig bundle sealRead pkg →
                  UnaryHistory outerRead ∧ UnaryHistory innerRead ∧
                    UnaryHistory arithmeticRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory sealRead ∧ Cont eps mu outerRead ∧
                        Cont outerRead delta innerRead ∧ Cont innerRead A arithmeticRead ∧
                          Cont arithmeticRead R readbackRead ∧
                            Cont readbackRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro rows outerRoute innerRoute arithmeticRoute readbackRoute sealRoute sealPkg
  obtain ⟨muUnary, _nuUnary, _wmuUnary, _wnuUnary, epsUnary, deltaUnary, rUnary,
    aUnary, eUnary, _hUnary, _cUnary, pUnary, _nUnary, provenancePkg⟩ := rows
  have outerUnary : UnaryHistory outerRead :=
    unary_cont_closed epsUnary muUnary outerRoute
  have innerUnary : UnaryHistory innerRead :=
    unary_cont_closed outerUnary deltaUnary innerRoute
  have arithmeticUnary : UnaryHistory arithmeticRead :=
    unary_cont_closed innerUnary aUnary arithmeticRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed arithmeticUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  exact
    ⟨outerUnary, innerUnary, arithmeticUnary, readbackUnary, sealUnary, outerRoute,
      innerRoute, arithmeticRoute, readbackRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.ModulusCompositionScheduleUp
