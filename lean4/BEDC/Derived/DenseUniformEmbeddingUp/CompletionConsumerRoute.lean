import BEDC.Derived.DenseUniformEmbeddingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DenseUniformEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DenseUniformEmbeddingCarrier_completion_consumer_route [AskSetup] [PackageSetup]
    {S T I Q M E _U _H _C _P _N denseRead modulusRead handoffRead targetRead
      extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory I →
        UnaryHistory Q →
          UnaryHistory M →
            UnaryHistory T →
              UnaryHistory E →
                Cont S I denseRead →
                  Cont denseRead Q modulusRead →
                    Cont modulusRead M handoffRead →
                      Cont handoffRead T targetRead →
                        Cont targetRead E extensionRead →
                          PkgSig bundle extensionRead pkg →
                            UnaryHistory denseRead ∧ UnaryHistory modulusRead ∧
                              UnaryHistory handoffRead ∧ UnaryHistory targetRead ∧
                                UnaryHistory extensionRead ∧ Cont S I denseRead ∧
                                  Cont denseRead Q modulusRead ∧
                                    Cont modulusRead M handoffRead ∧
                                      Cont handoffRead T targetRead ∧
                                        Cont targetRead E extensionRead ∧
                                          PkgSig bundle extensionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro sourceUnary imageUnary modulusUnary handoffUnary targetUnary extensionUnary denseCont
    modulusCont handoffCont targetCont extensionCont extensionPkg
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed sourceUnary imageUnary denseCont
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed denseUnary modulusUnary modulusCont
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed modulusReadUnary handoffUnary handoffCont
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed handoffReadUnary targetUnary targetCont
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed targetReadUnary extensionUnary extensionCont
  exact
    ⟨denseUnary, modulusReadUnary, handoffReadUnary, targetReadUnary, extensionReadUnary,
      denseCont, modulusCont, handoffCont, targetCont, extensionCont, extensionPkg⟩

end BEDC.Derived.DenseUniformEmbeddingUp
