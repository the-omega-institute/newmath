import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedIntervalPacket [AskSetup] [PackageSetup]
    (lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rationalCells ∧
    UnaryHistory dyadicRefinements ∧ UnaryHistory streamWindows ∧ UnaryHistory readbacks ∧
      UnaryHistory seals ∧ UnaryHistory nameCert ∧ Cont lower upper rationalCells ∧
        Cont rationalCells dyadicRefinements endpoint ∧ Cont streamWindows readbacks transport ∧
          Cont transport seals routes ∧ Cont routes nameCert provenance ∧
            PkgSig bundle endpoint pkg

theorem LocatedIntervalPacket_endpoint_transport [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint lower' upper' rationalCells' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          Cont lower' upper' rationalCells' ->
            Cont rationalCells' dyadicRefinements endpoint' ->
              PkgSig bundle endpoint' pkg ->
                LocatedIntervalPacket lower' upper' rationalCells' dyadicRefinements
                    streamWindows readbacks seals transport routes provenance nameCert endpoint'
                    bundle pkg ∧
                  hsame rationalCells rationalCells' ∧ hsame endpoint endpoint' := by
  intro packet sameLower sameUpper rationalCellsRoute endpointRoute endpointPkg
  obtain ⟨lowerUnary, upperUnary, rationalCellsUnary, dyadicUnary, windowsUnary,
    readbacksUnary, sealsUnary, nameCertUnary, rationalCellsOld, endpointOld,
    transportRoute, routesRoute, provenanceRoute, _endpointPkg⟩ := packet
  have lowerUnary' : UnaryHistory lower' :=
    unary_transport lowerUnary sameLower
  have upperUnary' : UnaryHistory upper' :=
    unary_transport upperUnary sameUpper
  have rationalCellsUnary' : UnaryHistory rationalCells' :=
    unary_cont_closed lowerUnary' upperUnary' rationalCellsRoute
  have sameRationalCells : hsame rationalCells rationalCells' :=
    cont_respects_hsame sameLower sameUpper rationalCellsOld rationalCellsRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed rationalCellsUnary' dyadicUnary endpointRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRationalCells (hsame_refl dyadicRefinements) endpointOld
      endpointRoute
  exact
    ⟨⟨lowerUnary', upperUnary', rationalCellsUnary', dyadicUnary, windowsUnary, readbacksUnary,
        sealsUnary, nameCertUnary, rationalCellsRoute, endpointRoute, transportRoute,
        routesRoute, provenanceRoute, endpointPkg⟩,
      sameRationalCells, sameEndpoint⟩

theorem LocatedIntervalPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows
              readbacks seals transport routes provenance nameCert endpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows
              readbacks seals transport routes provenance nameCert endpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows
              readbacks seals transport routes provenance nameCert endpoint bundle pkg ∧
            hsame row nameCert)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.LocatedIntervalUp
