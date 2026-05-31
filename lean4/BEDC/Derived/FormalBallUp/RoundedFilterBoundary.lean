import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_rounded_filter_boundary_certificate [AskSetup] [PackageSetup]
    {M R D W H C P N roundedBoundary transportedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont W C roundedBoundary ->
        Cont roundedBoundary H transportedRead ->
          Cont transportedRead N namedRead ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row roundedBoundary ∨ hsame row transportedRead ∨
                          hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W C roundedBoundary ∧
                      Cont roundedBoundary H transportedRead ∧
                        Cont transportedRead N namedRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory roundedBoundary ∧ UnaryHistory transportedRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier roundedBoundaryRoute transportedRoute namedRoute namedPkg
  obtain ⟨_metricUnary, _radiusUnary, _dyadicUnary, windowUnary, transportUnary,
    replayUnary, _provenanceUnary, nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have roundedBoundaryUnary : UnaryHistory roundedBoundary :=
    unary_cont_closed windowUnary replayUnary roundedBoundaryRoute
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_cont_closed roundedBoundaryUnary transportUnary transportedRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed transportedReadUnary nameCertUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row roundedBoundary ∨ hsame row transportedRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W C roundedBoundary ∧
              Cont roundedBoundary H transportedRead ∧ Cont transportedRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, roundedBoundaryRoute, transportedRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, roundedBoundaryUnary, transportedReadUnary, namedReadUnary⟩

end BEDC.Derived.FormalBallUp
