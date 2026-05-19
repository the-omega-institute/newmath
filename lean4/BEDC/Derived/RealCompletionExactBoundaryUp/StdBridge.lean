import BEDC.Derived.RealCompletionExactBoundaryUp.FourFaceExactness

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryUp_StdBridge [AskSetup] [PackageSetup]
    {limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance name sealClassifier witnessBudget streamReg terminalRead fourFaceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory limitSeal →
      UnaryHistory classifier →
        UnaryHistory witness →
          UnaryHistory synchronizer →
            UnaryHistory window →
              UnaryHistory readback →
                UnaryHistory dyadic →
                  UnaryHistory terminal →
                    Cont limitSeal classifier sealClassifier →
                      Cont witness synchronizer witnessBudget →
                        Cont window readback streamReg →
                          Cont dyadic terminal terminalRead →
                            Cont streamReg terminalRead fourFaceRead →
                              PkgSig bundle fourFaceRead pkg →
                                realCompletionExactBoundaryFields
                                    (RealCompletionExactBoundaryUp.mk limitSeal classifier
                                      witness synchronizer window readback dyadic terminal
                                      transport replay provenance name) =
                                  [limitSeal, classifier, witness, synchronizer, window,
                                    readback, dyadic, terminal, transport, replay, provenance,
                                    name] ∧
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row fourFaceRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row streamReg ∨ hsame row terminalRead ∨
                                        hsame row fourFaceRead)
                                    (fun row : BHist =>
                                      PkgSig bundle fourFaceRead pkg ∧
                                        hsame row fourFaceRead)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro limitSealUnary classifierUnary witnessUnary synchronizerUnary windowUnary
    readbackUnary dyadicUnary terminalUnary sealRoute witnessRoute streamRoute terminalRoute
    fourFaceRoute fourFacePkg
  have fourFace :
      UnaryHistory sealClassifier ∧ UnaryHistory witnessBudget ∧ UnaryHistory streamReg ∧
        UnaryHistory terminalRead ∧ UnaryHistory fourFaceRead ∧
          SemanticNameCert
            (fun row : BHist => hsame row fourFaceRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row streamReg ∨ hsame row terminalRead ∨ hsame row fourFaceRead)
            (fun row : BHist => PkgSig bundle fourFaceRead pkg ∧ hsame row fourFaceRead)
            hsame :=
    @RealCompletionExactBoundaryFourFaceExactness _ _ limitSeal classifier witness
      synchronizer window readback dyadic terminal transport replay provenance name sealClassifier
      witnessBudget streamReg terminalRead fourFaceRead bundle pkg limitSealUnary classifierUnary
      witnessUnary synchronizerUnary windowUnary readbackUnary dyadicUnary terminalUnary sealRoute
      witnessRoute streamRoute terminalRoute fourFaceRoute fourFacePkg
  obtain ⟨_sealUnary, _witnessBudgetUnary, _streamUnary, _terminalReadUnary,
    _fourFaceUnary, cert⟩ := fourFace
  exact ⟨rfl, cert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
