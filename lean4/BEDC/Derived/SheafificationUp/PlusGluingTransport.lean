import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPlusGluingTransport [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localRead gluingRead transportedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L localRead →
        Cont localRead G gluingRead →
          hsame transportedRead gluingRead →
            Cont transportedRead R replayRead →
              PkgSig bundle Q pkg →
                PkgSig bundle N pkg →
                  UnaryHistory localRead ∧ UnaryHistory gluingRead ∧
                    UnaryHistory transportedRead ∧ UnaryHistory replayRead ∧
                      Cont P L localRead ∧ Cont localRead G gluingRead ∧
                        Cont transportedRead R replayRead ∧ PkgSig bundle Q pkg ∧
                          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier localRoute gluingRoute sameTransport replayRoute qPkg namePkg
  obtain ⟨_CUnary, _TUnary, _JUnary, PUnary, LUnary, GUnary, _SUnary, _HUnary, RUnary,
    _QUnary, _NUnary, _carrierQPkg, _carrierNamePkg⟩ := carrier
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed PUnary LUnary localRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localUnary GUnary gluingRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport gluingUnary (hsame_symm sameTransport)
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary RUnary replayRoute
  exact
    ⟨localUnary, gluingUnary, transportedUnary, replayUnary, localRoute,
      gluingRoute, replayRoute, qPkg, namePkg⟩

end BEDC.Derived.SheafificationUp
