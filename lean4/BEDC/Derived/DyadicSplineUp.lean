import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicSplineUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicSplineFiniteCarrier [AskSetup] [PackageSetup]
    (k a l i q r h c p n endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory k ∧ UnaryHistory a ∧ UnaryHistory l ∧ UnaryHistory i ∧
    UnaryHistory q ∧ UnaryHistory r ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory n ∧ UnaryHistory endpoint ∧ Cont k a l ∧
        Cont i q r ∧ Cont h c p ∧ Cont l r endpoint ∧ PkgSig bundle endpoint pkg

theorem DyadicSplineFiniteCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {k a l i q r h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  intro carrier
  constructor
  · constructor
    · exact Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row row' same source
      exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
  · intro row source
    exact source
  · intro row source
    exact source

def DyadicSplinePacket [AskSetup] [PackageSetup]
    (knots coeffs segments cells readback «seal» transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory knots ∧ UnaryHistory coeffs ∧ UnaryHistory segments ∧
    Cont knots segments cells ∧ Cont cells coeffs readback ∧
      Cont readback «seal» provenance ∧ PkgSig bundle provenance pkg ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory nameCert

theorem DyadicSplinePacket_mesh_refinement_handoff [AskSetup] [PackageSetup]
    {knots coeffs segments cells readback «seal» transport route provenance nameCert refinedKnots
      refinedCoeffs refinedSegments refinedCells refinedReadback refinedProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSplinePacket knots coeffs segments cells readback «seal» transport route provenance
        nameCert bundle pkg ->
      hsame knots refinedKnots ->
        hsame coeffs refinedCoeffs ->
          hsame segments refinedSegments ->
            Cont refinedKnots refinedSegments refinedCells ->
              Cont refinedCells refinedCoeffs refinedReadback ->
                Cont refinedReadback «seal» refinedProvenance ->
                  PkgSig bundle refinedProvenance pkg ->
                    DyadicSplinePacket refinedKnots refinedCoeffs refinedSegments refinedCells
                        refinedReadback «seal» transport route refinedProvenance nameCert bundle pkg ∧
                      hsame cells refinedCells ∧ hsame readback refinedReadback ∧
                        hsame provenance refinedProvenance := by
  intro packet sameKnots sameCoeffs sameSegments refinedCellRoute refinedReadbackRoute
    refinedProvenanceRoute refinedPkg
  have knotsUnary : UnaryHistory knots :=
    packet.left
  have coeffsUnary : UnaryHistory coeffs :=
    packet.right.left
  have segmentsUnary : UnaryHistory segments :=
    packet.right.right.left
  have cellRoute : Cont knots segments cells :=
    packet.right.right.right.left
  have readbackRoute : Cont cells coeffs readback :=
    packet.right.right.right.right.left
  have provenanceRoute : Cont readback «seal» provenance :=
    packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.right.right.right.right.right.left
  have nameCertUnary : UnaryHistory nameCert :=
    packet.right.right.right.right.right.right.right.right.right
  have refinedKnotsUnary : UnaryHistory refinedKnots :=
    unary_transport knotsUnary sameKnots
  have refinedCoeffsUnary : UnaryHistory refinedCoeffs :=
    unary_transport coeffsUnary sameCoeffs
  have refinedSegmentsUnary : UnaryHistory refinedSegments :=
    unary_transport segmentsUnary sameSegments
  have sameCells : hsame cells refinedCells :=
    cont_respects_hsame sameKnots sameSegments cellRoute refinedCellRoute
  have sameReadback : hsame readback refinedReadback :=
    cont_respects_hsame sameCells sameCoeffs readbackRoute refinedReadbackRoute
  have sameProvenance : hsame provenance refinedProvenance :=
    cont_respects_hsame sameReadback (hsame_refl «seal») provenanceRoute refinedProvenanceRoute
  have refinedPacket :
      DyadicSplinePacket refinedKnots refinedCoeffs refinedSegments refinedCells refinedReadback
        «seal» transport route refinedProvenance nameCert bundle pkg := by
    exact
      ⟨refinedKnotsUnary,
        refinedCoeffsUnary,
        refinedSegmentsUnary,
        refinedCellRoute,
        refinedReadbackRoute,
        refinedProvenanceRoute,
        refinedPkg,
        transportUnary,
        routeUnary,
        nameCertUnary⟩
  exact ⟨refinedPacket, sameCells, sameReadback, sameProvenance⟩

end BEDC.Derived.DyadicSplineUp
