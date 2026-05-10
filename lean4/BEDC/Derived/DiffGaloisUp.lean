import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffGaloisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def DiffGaloisPicardVessiotPacket [AskSetup] [PackageSetup]
    (differentialField operatorCoefficients seqBasis fundamentalSolution galoisAction
      constantField solutionLedger actionLedger endpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory differentialField ∧
    UnaryHistory operatorCoefficients ∧
      UnaryHistory seqBasis ∧
        UnaryHistory fundamentalSolution ∧
          UnaryHistory galoisAction ∧
            UnaryHistory constantField ∧
              Cont seqBasis fundamentalSolution solutionLedger ∧
                Cont differentialField operatorCoefficients actionLedger ∧
                  Cont solutionLedger actionLedger endpoint ∧
                    SigRel bundle endpoint provenance ∧
                      PkgSig bundle provenance pkg

theorem DiffGaloisPicardVessiotPacket_solution_space_obligation [AskSetup] [PackageSetup]
    {differentialField operatorCoefficients seqBasis fundamentalSolution galoisAction
      constantField solutionLedger actionLedger endpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiffGaloisPicardVessiotPacket differentialField operatorCoefficients seqBasis
      fundamentalSolution galoisAction constantField solutionLedger actionLedger endpoint
      provenance bundle pkg ->
        UnaryHistory solutionLedger ∧
          UnaryHistory actionLedger ∧
            UnaryHistory endpoint ∧
              hsame solutionLedger (append seqBasis fundamentalSolution) ∧
                hsame actionLedger (append differentialField operatorCoefficients) ∧
                  hsame endpoint (append solutionLedger actionLedger) ∧
                    SigRel bundle endpoint provenance ∧
                      PkgSig bundle provenance pkg := by
  intro packet
  have solutionUnary : UnaryHistory solutionLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.left
  have actionUnary : UnaryHistory actionLedger :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed solutionUnary actionUnary
      packet.right.right.right.right.right.right.right.right.left
  exact And.intro solutionUnary
    (And.intro actionUnary
      (And.intro endpointUnary
        (And.intro packet.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.right.right.left
                packet.right.right.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.DiffGaloisUp
