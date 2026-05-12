import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HausdorffCompletionCarrier [AskSetup] [PackageSetup]
    (source entourage separated handoff transport route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
    UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ Cont source entourage transport ∧
        Cont separated handoff route ∧ Cont transport route provenance ∧
          PkgSig bundle provenance pkg

theorem HausdorffCompletionCarrier_classifier_transport [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance source' entourage'
      separated' handoff' transport' route' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      hsame source source' ->
        hsame entourage entourage' ->
          hsame separated separated' ->
            hsame handoff handoff' ->
              hsame transport transport' ->
                Cont separated' handoff' route' ->
                  Cont transport' route' provenance' ->
                    PkgSig bundle provenance' pkg ->
                      HausdorffCompletionCarrier source' entourage' separated' handoff'
                          transport' route' provenance' bundle pkg ∧
                        hsame route route' := by
  intro carrier sameSource sameEntourage sameSeparated sameHandoff sameTransport routeRow'
    provenanceRow' provenancePkg'
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary, routeUnary,
    provenanceUnary, sourceEntourageRow, routeRow, provenanceRow, _provenancePkg⟩ := carrier
  have transportRow' : Cont source' entourage' transport' :=
    cont_intro
      (sameTransport.symm.trans
        (cont_respects_hsame sameSource sameEntourage sourceEntourageRow (cont_intro rfl)))
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameSeparated sameHandoff routeRow routeRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameRoute provenanceRow provenanceRow'
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have entourageUnary' : UnaryHistory entourage' := unary_transport entourageUnary sameEntourage
  have separatedUnary' : UnaryHistory separated' := unary_transport separatedUnary sameSeparated
  have handoffUnary' : UnaryHistory handoff' := unary_transport handoffUnary sameHandoff
  have transportUnary' : UnaryHistory transport' := unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨sourceUnary', entourageUnary', separatedUnary', handoffUnary', transportUnary',
        routeUnary', provenanceUnary', transportRow', routeRow', provenanceRow',
        provenancePkg'⟩,
      sameRoute⟩

end BEDC.Derived.HausdorffCompletionUp
