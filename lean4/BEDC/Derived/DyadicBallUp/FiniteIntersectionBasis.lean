import BEDC.Derived.DyadicBallUp

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicBallFiniteWindowPacket_finite_intersection_basis_package [AskSetup]
    [PackageSetup]
    {center radius schedule observation containment route provenance certRow handoff
      sealBoundary terminalRadius terminalContainment terminalHandoff terminalCertRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteWindowPacket center radius schedule observation containment route
        provenance certRow handoff sealBoundary bundle pkg ->
      UnaryHistory terminalRadius ->
        Cont center terminalRadius terminalContainment ->
          Cont terminalContainment route terminalHandoff ->
            Cont terminalHandoff provenance terminalCertRow ->
              Cont terminalHandoff sealBoundary terminalCertRow ->
                PkgSig bundle terminalHandoff pkg ->
                  forall chainRows : List BHist,
                    (forall row : BHist, row ∈ chainRows -> UnaryHistory row) ->
                      UnaryHistory (chainRows.foldl append terminalHandoff) ∧
                        hsame terminalHandoff (append terminalContainment route) ∧
                          PkgSig bundle terminalHandoff pkg := by
  intro packet terminalRadiusUnary terminalContainmentRoute terminalHandoffRoute
  intro _terminalProvenanceRoute _terminalSealRoute terminalPkg chainRows
  obtain ⟨centerUnary, _radiusUnary, scheduleUnary, observationUnary, _provenanceUnary,
    _certUnary, _sealUnary, _containmentRow, routeRow, _handoffRow, _provenanceRow,
    _sealRow, _pkgRow⟩ := packet
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary observationUnary routeRow
  have terminalContainmentUnary : UnaryHistory terminalContainment :=
    unary_cont_closed centerUnary terminalRadiusUnary terminalContainmentRoute
  have terminalHandoffUnary : UnaryHistory terminalHandoff :=
    unary_cont_closed terminalContainmentUnary routeUnary terminalHandoffRoute
  have foldClosed :
      forall base : BHist,
        UnaryHistory base ->
          (forall row : BHist, row ∈ chainRows -> UnaryHistory row) ->
            UnaryHistory (chainRows.foldl append base) := by
    induction chainRows with
    | nil =>
        intro base baseUnary _rowUnary
        exact baseUnary
    | cons row tail ih =>
        intro base baseUnary rowUnary
        have rowHeadUnary : UnaryHistory row :=
          rowUnary row (List.Mem.head tail)
        have nextUnary : UnaryHistory (append base row) :=
          unary_append_closed baseUnary rowHeadUnary
        exact ih (append base row) nextUnary
          (fun later laterInTail => rowUnary later (List.Mem.tail row laterInTail))
  intro rowUnary
  exact ⟨foldClosed terminalHandoff terminalHandoffUnary rowUnary, terminalHandoffRoute,
    terminalPkg⟩

end BEDC.Derived.DyadicBallUp
