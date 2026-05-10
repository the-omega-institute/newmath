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

theorem SpectralSeqBHistPageCarrier_filtration_transport [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint page'
      differential' readback' transition' endpoint' filtrationExtension : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence transition
        provenance endpoint bundle pkg ->
      hsame page page' ->
        hsame differential differential' ->
          Cont page' differential' readback' ->
            Cont readback' convergence transition' ->
              Cont provenance transition' endpoint' ->
                Cont transition' convergence filtrationExtension ->
                  SpectralSeqBHistPageCarrier abelian homology page' differential' readback'
                      convergence transition' provenance endpoint' bundle pkg ∧
                    UnaryHistory filtrationExtension ∧
                      hsame filtrationExtension (append transition' convergence) ∧
                        hsame readback readback' ∧ hsame transition transition' := by
  intro carrier samePage sameDifferential successorReadback successorTransition successorEndpoint
    filtrationRow
  have successor :=
    SpectralSeqBHistPageCarrier_successor_page_closure carrier samePage sameDifferential
      successorReadback successorTransition successorEndpoint
  have obligation := SpectralSeqBHistPageCarrier_obligation_surface successor.left
  have filtrationUnary : UnaryHistory filtrationExtension :=
    unary_cont_closed obligation.right.right.right.left
      successor.left.right.right.right.right.left filtrationRow
  exact And.intro successor.left
    (And.intro filtrationUnary
      (And.intro filtrationRow
        (And.intro successor.right.left successor.right.right)))

theorem SpectralSeqBHistPageCarrier_zero_page_carrier [AskSetup] [PackageSetup]
    {source provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory provenance ->
        PkgSig bundle (append provenance source) pkg ->
          SpectralSeqBHistPageCarrier source source source BHist.Empty source BHist.Empty
            source provenance (append provenance source) bundle pkg := by
  intro sourceUnary provenanceUnary pkgSig
  exact And.intro sourceUnary
    (And.intro sourceUnary
      (And.intro sourceUnary
        (And.intro unary_empty
          (And.intro unary_empty
            (And.intro provenanceUnary
              (And.intro (cont_right_unit source)
                (And.intro (cont_right_unit source)
                  (And.intro rfl pkgSig))))))))

theorem SpectralSeqBHistPageCarrier_derivedfunctor_consumer_surface [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint
      consumer surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence transition
        provenance endpoint bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint consumer surface ->
          UnaryHistory surface ∧ hsame surface (append endpoint consumer) ∧
            UnaryHistory transition ∧ hsame endpoint (append provenance transition) ∧
              PkgSig bundle endpoint pkg := by
  intro carrier consumerUnary surfaceRow
  have obligation := SpectralSeqBHistPageCarrier_obligation_surface carrier
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed obligation.right.right.right.right.left consumerUnary surfaceRow
  exact And.intro surfaceUnary
    (And.intro surfaceRow
      (And.intro obligation.right.right.right.left
        (And.intro obligation.right.right.right.right.right.right.right.left
          obligation.right.right.right.right.right.right.right.right)))

theorem SpectralSeqBHistPageCarrier_visible_target_filtration_coverage
    [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint target :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence transition
        provenance endpoint bundle pkg ->
      Cont transition endpoint target ->
        UnaryHistory target ∧ hsame target (append transition endpoint) ∧
          hsame transition (append readback convergence) ∧
            hsame endpoint (append provenance transition) ∧ PkgSig bundle endpoint pkg := by
  intro carrier targetRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have transitionUnary : UnaryHistory transition :=
    unary_cont_closed readbackUnary carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left transitionUnary
      carrier.right.right.right.right.right.right.right.right.left
  have targetUnary : UnaryHistory target :=
    unary_cont_closed transitionUnary endpointUnary targetRow
  exact And.intro targetUnary
    (And.intro targetRow
      (And.intro carrier.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right.left
          carrier.right.right.right.right.right.right.right.right.right)))

theorem SpectralSeqBHistPageCarrier_cont_page_ledger_closure [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint
      finalEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : SpectralSeqBHistPageCarrier abelian homology page differential readback
      convergence transition provenance endpoint bundle pkg) (steps : List BHist)
    (stepsUnary : forall row : BHist, List.Mem row steps -> UnaryHistory row)
    (finalRow : Cont (List.foldl append transition steps) provenance finalEndpoint) :
    UnaryHistory (List.foldl append transition steps) ∧ UnaryHistory finalEndpoint ∧
      hsame finalEndpoint (append (List.foldl append transition steps) provenance) ∧
        PkgSig bundle endpoint pkg := by
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have transitionUnary : UnaryHistory transition :=
    unary_cont_closed readbackUnary carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have foldedUnaryFrom :
      forall rows : List BHist, forall acc : BHist, UnaryHistory acc ->
        (forall row : BHist, List.Mem row rows -> UnaryHistory row) ->
          UnaryHistory (List.foldl append acc rows) := by
    intro rows
    induction rows with
    | nil =>
        intro acc accUnary _rowsUnary
        exact accUnary
    | cons row rows ih =>
        intro acc accUnary rowsUnary
        have rowUnary : UnaryHistory row :=
          rowsUnary row (List.Mem.head rows)
        have tailRowsUnary : forall tailRow : BHist, List.Mem tailRow rows -> UnaryHistory tailRow :=
          by
            intro tailRow tailMem
            exact rowsUnary tailRow (List.Mem.tail row tailMem)
        exact ih (append acc row) (unary_append_closed accUnary rowUnary) tailRowsUnary
  have foldedUnary : UnaryHistory (List.foldl append transition steps) :=
    foldedUnaryFrom steps transition transitionUnary stepsUnary
  have finalUnary : UnaryHistory finalEndpoint :=
    unary_cont_closed foldedUnary carrier.right.right.right.right.right.left finalRow
  exact And.intro foldedUnary
    (And.intro finalUnary
      (And.intro finalRow carrier.right.right.right.right.right.right.right.right.right))

theorem SpectralSeqBHistPageCarrier_identity_transition_ledger [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint
      identityTransition identityEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence
        transition provenance endpoint bundle pkg ->
      Cont transition page identityTransition ->
        Cont provenance identityTransition identityEndpoint ->
          PkgSig bundle identityEndpoint pkg ->
            UnaryHistory identityTransition ∧ UnaryHistory identityEndpoint ∧
              hsame identityTransition (append transition page) ∧
                hsame identityEndpoint (append provenance identityTransition) ∧
                  PkgSig bundle identityEndpoint pkg := by
  intro carrier identityTransitionRow identityEndpointRow identityPkg
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have transitionUnary : UnaryHistory transition :=
    unary_cont_closed readbackUnary carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have identityTransitionUnary : UnaryHistory identityTransition :=
    unary_cont_closed transitionUnary carrier.right.right.left identityTransitionRow
  have identityEndpointUnary : UnaryHistory identityEndpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left identityTransitionUnary
      identityEndpointRow
  exact And.intro identityTransitionUnary
    (And.intro identityEndpointUnary
      (And.intro identityTransitionRow (And.intro identityEndpointRow identityPkg)))

theorem SpectralSeqBHistPageCarrier_convergence_boundary [AskSetup] [PackageSetup]
    {abelian homology page differential readback convergence transition provenance endpoint target :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence
        transition provenance endpoint bundle pkg ->
      Cont convergence endpoint target ->
        UnaryHistory convergence ∧ UnaryHistory transition ∧ UnaryHistory endpoint ∧
          UnaryHistory target ∧ hsame transition (append readback convergence) ∧
            hsame endpoint (append provenance transition) ∧
              hsame target (append convergence endpoint) ∧ PkgSig bundle endpoint pkg := by
  intro carrier targetRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have transitionUnary : UnaryHistory transition :=
    unary_cont_closed readbackUnary carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left transitionUnary
      carrier.right.right.right.right.right.right.right.right.left
  have targetUnary : UnaryHistory target :=
    unary_cont_closed carrier.right.right.right.right.left endpointUnary targetRow
  exact And.intro carrier.right.right.right.right.left
    (And.intro transitionUnary
      (And.intro endpointUnary
        (And.intro targetUnary
          (And.intro carrier.right.right.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.right.left
              (And.intro targetRow
                carrier.right.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.SpectralSeqUp
