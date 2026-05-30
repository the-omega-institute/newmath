import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_radius_order_scope_package [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead closedBallRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont radiusRead W closedBallRead ->
          Cont closedBallRead C realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
                      hsame row C ∨ hsame row realRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg ∧
                      hsame row realRead)
                  hsame ∧
                UnaryHistory radiusRead ∧ UnaryHistory closedBallRead ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier radiusRoute closedBallRoute realRoute realPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary, replayUnary,
    _provenanceUnary, _nameCertUnary, _metricRadius, _windowReplay, _transportReplay,
    provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have closedBallReadUnary : UnaryHistory closedBallRead :=
    unary_cont_closed radiusReadUnary windowUnary closedBallRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed closedBallReadUnary replayUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
              hsame row C ∨ hsame row realRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg ∧
              hsame row realRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact ⟨provenancePkg, realPkg, source.left⟩
  }
  exact ⟨cert, radiusReadUnary, closedBallReadUnary, realReadUnary⟩

end BEDC.Derived.FormalBallUp
