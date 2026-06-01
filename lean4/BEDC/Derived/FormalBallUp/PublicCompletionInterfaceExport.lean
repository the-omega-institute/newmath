import BEDC.Derived.FormalBallUp.ObligationClosureExport

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_public_completion_interface_export [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead boundaryRead completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont D W boundaryRead ->
          Cont boundaryRead C completionRead ->
            Cont completionRead N publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
                        hsame row completionRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory radiusRead ∧ UnaryHistory boundaryRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier radiusRoute boundaryRoute completionRoute publicRoute publicPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, provenanceUnary, nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed dyadicUnary windowUnary boundaryRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryReadUnary replayUnary completionRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed completionReadUnary nameCertUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
              hsame row completionRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, publicPkg⟩
  }
  exact
    ⟨cert, radiusReadUnary, boundaryReadUnary, completionReadUnary, publicReadUnary⟩

end BEDC.Derived.FormalBallUp
