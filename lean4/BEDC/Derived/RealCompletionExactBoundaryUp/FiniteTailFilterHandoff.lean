import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryFiniteTailFilterHandoff [AskSetup] [PackageSetup]
    {limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance name finiteTail streamReg terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realCompletionExactBoundaryFields
        (RealCompletionExactBoundaryUp.mk limitSeal classifier witness synchronizer window readback
          dyadic terminal transport replay provenance name) =
      [limitSeal, classifier, witness, synchronizer, window, readback, dyadic, terminal,
        transport, replay, provenance, name] →
      UnaryHistory finiteTail →
        UnaryHistory window →
          UnaryHistory readback →
            UnaryHistory dyadic →
              UnaryHistory terminal →
                Cont window readback streamReg →
                  Cont dyadic terminal terminalRead →
                    Cont finiteTail streamReg terminalRead →
                      PkgSig bundle terminalRead pkg →
                        realCompletionExactBoundaryFields
                            (RealCompletionExactBoundaryUp.mk limitSeal classifier witness
                              synchronizer window readback dyadic terminal transport replay
                              provenance name) =
                          [limitSeal, classifier, witness, synchronizer, window, readback, dyadic,
                            terminal, transport, replay, provenance, name] ∧
                          UnaryHistory streamReg ∧ UnaryHistory terminalRead ∧
                            Cont window readback streamReg ∧ Cont dyadic terminal terminalRead ∧
                              Cont finiteTail streamReg terminalRead ∧
                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro fields finiteTailUnary windowUnary readbackUnary dyadicUnary terminalUnary streamCont
    terminalCont tailCont terminalPkg
  have streamRegUnary : UnaryHistory streamReg :=
    unary_cont_closed windowUnary readbackUnary streamCont
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed dyadicUnary terminalUnary terminalCont
  exact
    ⟨fields, streamRegUnary, terminalReadUnary, streamCont, terminalCont, tailCont, terminalPkg⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
