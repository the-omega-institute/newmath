import BEDC.Derived.IshiharaTrickUp.BranchStability

namespace BEDC.Derived.IshiharaTrickUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IshiharaTrickBoundedSequenceRoute [AskSetup] [PackageSetup]
    {finiteTest branch boundedSequence realSeal replay provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory finiteTest →
      UnaryHistory branch →
        UnaryHistory realSeal →
          UnaryHistory provenance →
            Cont finiteTest branch boundedSequence →
              Cont boundedSequence realSeal replay →
                Cont replay provenance endpoint →
                  PkgSig bundle endpoint pkg →
                    UnaryHistory boundedSequence ∧ UnaryHistory replay ∧
                      UnaryHistory endpoint ∧ Cont finiteTest branch boundedSequence ∧
                        Cont boundedSequence realSeal replay ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro finiteUnary branchUnary realSealUnary provenanceUnary finiteBranch boundedReal
    replayProvenance endpointPkg
  have boundedUnary : UnaryHistory boundedSequence :=
    unary_cont_closed finiteUnary branchUnary finiteBranch
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed boundedUnary realSealUnary boundedReal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  exact
    ⟨boundedUnary, replayUnary, endpointUnary, finiteBranch, boundedReal, endpointPkg⟩

end BEDC.Derived.IshiharaTrickUp
