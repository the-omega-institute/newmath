import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPlusGluingReplay [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localityRead gluingRead sheafReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont L G localityRead →
        Cont localityRead S gluingRead →
          Cont gluingRead R sheafReplay →
            PkgSig bundle sheafReplay pkg →
              UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory S ∧ UnaryHistory R ∧
                UnaryHistory localityRead ∧ UnaryHistory gluingRead ∧
                  UnaryHistory sheafReplay ∧ Cont L G localityRead ∧
                    Cont localityRead S gluingRead ∧ Cont gluingRead R sheafReplay ∧
                      PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                        PkgSig bundle sheafReplay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier localityRoute gluingRoute replayRoute replayPkg
  obtain ⟨_CUnary, _TUnary, _JUnary, _PUnary, LUnary, GUnary, SUnary, _HUnary, RUnary,
    _QUnary, _NUnary, qPkg, namePkg⟩ := carrier
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed LUnary GUnary localityRoute
  have gluingReadUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityReadUnary SUnary gluingRoute
  have sheafReplayUnary : UnaryHistory sheafReplay :=
    unary_cont_closed gluingReadUnary RUnary replayRoute
  exact
    ⟨LUnary, GUnary, SUnary, RUnary, localityReadUnary, gluingReadUnary,
      sheafReplayUnary, localityRoute, gluingRoute, replayRoute, qPkg, namePkg,
      replayPkg⟩

end BEDC.Derived.SheafificationUp
