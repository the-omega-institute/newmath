import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_rounded_filter_cauchyfilter_boundary [AskSetup] [PackageSetup]
    {M R D W H C P N roundedRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont D W roundedRead ->
        Cont roundedRead C cauchyRead ->
          PkgSig bundle cauchyRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
                    Cont roundedRead C cauchyRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ PkgSig bundle cauchyRead pkg ∧
                    hsame row cauchyRead)
                hsame ∧
              UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
                UnaryHistory C ∧ UnaryHistory roundedRead ∧ UnaryHistory cauchyRead ∧
                  Cont D W roundedRead ∧ Cont roundedRead C cauchyRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier roundedRoute cauchyRoute cauchyPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have roundedUnary : UnaryHistory roundedRead :=
    unary_cont_closed dyadicUnary windowUnary roundedRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed roundedUnary replayUnary cauchyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
              Cont roundedRead C cauchyRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle cauchyRead pkg ∧
              hsame row cauchyRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cauchyRead
        ⟨hsame_refl cauchyRead, cauchyUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr cauchyRoute)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, cauchyPkg, source.left⟩
  }
  exact
    ⟨cert, metricUnary, radiusUnary, dyadicUnary, windowUnary, replayUnary,
      roundedUnary, cauchyUnary, roundedRoute, cauchyRoute, provenancePkg, cauchyPkg⟩

end BEDC.Derived.FormalBallUp
