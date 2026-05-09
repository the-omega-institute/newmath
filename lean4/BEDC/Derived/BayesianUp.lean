import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BayesianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BayesianPosteriorPacket [AskSetup] [PackageSetup]
    (prior likelihood evidence posterior update normalisation provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
    UnaryHistory posterior ∧ Cont prior likelihood update ∧ Cont update evidence posterior ∧
      Cont evidence posterior normalisation ∧ Cont provenance normalisation endpoint ∧
        PkgSig bundle endpoint pkg

theorem BayesianPosteriorPacket_source_obligation [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior update normalisation provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
        endpoint bundle pkg ->
      UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
        UnaryHistory posterior ∧ Cont prior likelihood update ∧ Cont update evidence posterior ∧
          Cont evidence posterior normalisation ∧ hsame endpoint (append provenance normalisation) ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.left
                  packet.right.right.right.right.right.right.right.right)))))))

end BEDC.Derived.BayesianUp
