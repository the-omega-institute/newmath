import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BayesianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BayesianPosteriorSurface [AskSetup] [PackageSetup]
    (prior likelihood evidence posterior normalizer classifier provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
    Cont prior likelihood normalizer ∧ Cont normalizer evidence posterior ∧
      hsame classifier posterior ∧ PkgSig bundle provenance pkg

theorem BayesianPosteriorSurface_source_obligation [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior normalizer classifier provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorSurface prior likelihood evidence posterior normalizer classifier
      provenance bundle pkg ->
        UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
          UnaryHistory normalizer ∧ UnaryHistory posterior ∧
            Cont prior likelihood normalizer ∧ Cont normalizer evidence posterior ∧
              hsame classifier posterior ∧ PkgSig bundle provenance pkg := by
  intro surface
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.left
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed normalizerUnary surface.right.right.left
      surface.right.right.right.right.left
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro surface.right.right.left
        (And.intro normalizerUnary
          (And.intro posteriorUnary
            (And.intro surface.right.right.right.left
              (And.intro surface.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.left
                  surface.right.right.right.right.right.right)))))))

theorem BayesianPosteriorSurface_update_ledger_exactness [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior normalizer classifier provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorSurface prior likelihood evidence posterior normalizer classifier
      provenance bundle pkg ->
        Cont posterior provenance ledger -> UnaryHistory provenance ->
          UnaryHistory ledger ∧ hsame ledger (append posterior provenance) ∧
            hsame classifier posterior ∧ PkgSig bundle provenance pkg := by
  intro surface ledgerCont provenanceUnary
  have sourceRows :=
    BayesianPosteriorSurface_source_obligation surface
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceRows.right.right.right.right.left provenanceUnary ledgerCont
  exact And.intro ledgerUnary
    (And.intro ledgerCont
      (And.intro sourceRows.right.right.right.right.right.right.right.left
        sourceRows.right.right.right.right.right.right.right.right))

end BEDC.Derived.BayesianUp
