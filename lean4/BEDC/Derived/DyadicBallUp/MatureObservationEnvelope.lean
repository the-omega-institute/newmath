import BEDC.Derived.DyadicBallUp

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicBallFiniteWindowPacket_mature_observation_envelope [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} {reads : List BHist} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg ->
      (forall row : BHist, row ∈ reads -> UnaryHistory row) ->
        UnaryHistory (reads.foldl append certRow) ∧ UnaryHistory handoff ∧
          UnaryHistory sealBoundary ∧ PkgSig bundle handoff pkg := by
  intro packet readsUnary
  obtain ⟨centerUnary, radiusUnary, scheduleUnary, observationUnary, _provenanceUnary,
    certUnary, sealUnary, containmentRow, routeRow, handoffRow, _provenanceRow,
    _sealRow, pkgRow⟩ := packet
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed centerUnary radiusUnary containmentRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary observationUnary routeRow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed containmentUnary routeUnary handoffRow
  have foldClosed :
      forall rows : List BHist,
        (forall row : BHist, row ∈ rows -> UnaryHistory row) ->
          forall base : BHist, UnaryHistory base -> UnaryHistory (rows.foldl append base) := by
    intro rows rowsUnary
    induction rows with
    | nil =>
        intro base baseUnary
        exact baseUnary
    | cons read tail ih =>
        intro base baseUnary
        have readUnary : UnaryHistory read :=
          rowsUnary read (List.Mem.head tail)
        have tailUnary : forall row : BHist, row ∈ tail -> UnaryHistory row :=
          fun row rowInTail => rowsUnary row (List.Mem.tail read rowInTail)
        have nextUnary : UnaryHistory (append base read) :=
          unary_append_closed baseUnary readUnary
        exact ih tailUnary (append base read) nextUnary
  exact ⟨foldClosed reads readsUnary certRow certUnary, handoffUnary, sealUnary, pkgRow⟩

end BEDC.Derived.DyadicBallUp
