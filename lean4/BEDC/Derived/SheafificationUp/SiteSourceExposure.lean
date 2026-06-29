import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSiteSourceExposure [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont J P restrictionRead →
          Cont restrictionRead L localRead →
            PkgSig bundle Q pkg →
              PkgSig bundle N pkg →
                UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory J ∧ UnaryHistory P ∧
                  UnaryHistory L ∧ UnaryHistory coverWindow ∧
                    UnaryHistory restrictionRead ∧ UnaryHistory localRead ∧
                      Cont C T coverWindow ∧ Cont J P restrictionRead ∧
                        Cont restrictionRead L localRead ∧ PkgSig bundle Q pkg ∧
                          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRoute restrictionRoute localRoute qPkg namePkg
  obtain ⟨CUnary, TUnary, JUnary, PUnary, LUnary, _GUnary, _SUnary, _HUnary, _RUnary,
    _QUnary, _NUnary, _carrierQPkg, _carrierNamePkg⟩ := carrier
  have coverUnary : UnaryHistory coverWindow :=
    unary_cont_closed CUnary TUnary coverRoute
  have restrictionUnary : UnaryHistory restrictionRead :=
    unary_cont_closed JUnary PUnary restrictionRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed restrictionUnary LUnary localRoute
  exact
    ⟨CUnary, TUnary, JUnary, PUnary, LUnary, coverUnary, restrictionUnary,
      localUnary, coverRoute, restrictionRoute, localRoute, qPkg, namePkg⟩

end BEDC.Derived.SheafificationUp
