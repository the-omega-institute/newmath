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

theorem SpectralSeqBHistPageCarrier_successor_page_closure [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint page'
      differential' readback' transition' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence transition
        provenance endpoint bundle pkg ->
      hsame page page' ->
        hsame differential differential' ->
          Cont page' differential' readback' ->
            Cont readback' convergence transition' ->
              Cont provenance transition' endpoint' ->
              SpectralSeqBHistPageCarrier abelian homology page' differential' readback'
                  convergence transition' provenance endpoint' bundle pkg ∧
                hsame readback readback' ∧ hsame transition transition' := by
  intro carrier samePage sameDifferential successorReadback successorTransition successorEndpoint
  have pageUnary : UnaryHistory page' :=
    unary_transport carrier.right.right.left samePage
  have differentialUnary : UnaryHistory differential' :=
    unary_transport carrier.right.right.right.left sameDifferential
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame samePage sameDifferential
      carrier.right.right.right.right.right.right.left successorReadback
  have sameTransition : hsame transition transition' :=
    cont_respects_hsame sameReadback (hsame_refl convergence)
      carrier.right.right.right.right.right.right.right.left successorTransition
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameTransition
      carrier.right.right.right.right.right.right.right.right.left successorEndpoint
  have pkgSig' : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact carrier.right.right.right.right.right.right.right.right.right
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro pageUnary
          (And.intro differentialUnary
            (And.intro carrier.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.left
                (And.intro successorReadback
                  (And.intro successorTransition
                    (And.intro successorEndpoint pkgSig')))))))))
    (And.intro sameReadback sameTransition)

end BEDC.Derived.SpectralSeqUp
