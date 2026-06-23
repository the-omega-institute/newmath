import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSourceLocalityObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont J P restrictionRead →
          Cont coverWindow restrictionRead localityRead →
            PkgSig bundle localityRead pkg →
              UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory J ∧ UnaryHistory P ∧
                UnaryHistory L ∧ UnaryHistory coverWindow ∧ UnaryHistory restrictionRead ∧
                  UnaryHistory localityRead ∧ Cont C T coverWindow ∧
                    Cont J P restrictionRead ∧ Cont coverWindow restrictionRead localityRead ∧
                      PkgSig bundle N pkg ∧ PkgSig bundle localityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRoute restrictionRoute localityRoute localityPkg
  obtain ⟨CUnary, TUnary, JUnary, PUnary, LUnary, _GUnary, _SUnary, _HUnary, _RUnary,
    _QUnary, _NUnary, namePkg⟩ := carrier
  have coverUnary : UnaryHistory coverWindow :=
    unary_cont_closed CUnary TUnary coverRoute
  have restrictionUnary : UnaryHistory restrictionRead :=
    unary_cont_closed JUnary PUnary restrictionRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed coverUnary restrictionUnary localityRoute
  exact
    ⟨CUnary, TUnary, JUnary, PUnary, LUnary, coverUnary, restrictionUnary,
      localityUnary, coverRoute, restrictionRoute, localityRoute, namePkg, localityPkg⟩

end BEDC.Derived.SheafificationUp
