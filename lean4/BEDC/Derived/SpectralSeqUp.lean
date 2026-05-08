import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SpectralSeqUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpectralSeqBHistPageCarrier [AskSetup] [PackageSetup]
    (abelian homology page differential readback convergence transition provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory abelian ∧
    UnaryHistory homology ∧
      UnaryHistory page ∧
        UnaryHistory differential ∧
          UnaryHistory convergence ∧
            UnaryHistory provenance ∧
              Cont page differential readback ∧
                Cont readback convergence transition ∧
                  Cont provenance transition endpoint ∧
                    PkgSig bundle endpoint pkg

theorem SpectralSeqBHistPageCarrier_obligation_surface [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence
        transition provenance endpoint bundle pkg ->
      UnaryHistory page ∧ UnaryHistory differential ∧ UnaryHistory readback ∧
        UnaryHistory transition ∧ UnaryHistory endpoint ∧ Cont page differential readback ∧
          Cont readback convergence transition ∧ Cont provenance transition endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  have readbackRow : Cont page differential readback :=
    carrier.right.right.right.right.right.right.left
  have transitionRow : Cont readback convergence transition :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance transition endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left readbackRow
  have transitionUnary : UnaryHistory transition :=
    unary_cont_closed readbackUnary carrier.right.right.right.right.left transitionRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left transitionUnary endpointRow
  exact And.intro carrier.right.right.left
    (And.intro carrier.right.right.right.left
      (And.intro readbackUnary
        (And.intro transitionUnary
          (And.intro endpointUnary
            (And.intro readbackRow
              (And.intro transitionRow
                (And.intro endpointRow
                  carrier.right.right.right.right.right.right.right.right.right)))))))

end BEDC.Derived.SpectralSeqUp
