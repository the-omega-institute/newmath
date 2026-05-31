import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_radius_order_handoff [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead orderRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont radiusRead W orderRead ->
          Cont orderRead C completionRead ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
                      hsame row radiusRead ∨ hsame row orderRead ∨
                        Cont orderRead C completionRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg ∧
                      hsame row completionRead)
                  hsame ∧
                UnaryHistory radiusRead ∧ UnaryHistory orderRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier radiusRoute orderRoute completionRoute completionPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary, replayUnary,
    _provenanceUnary, _nameCertUnary, _metricRadius, _windowReplay, _transportReplay,
    provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed radiusReadUnary windowUnary orderRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed orderReadUnary replayUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
              hsame row radiusRead ∨ hsame row orderRead ∨ Cont orderRead C completionRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg ∧
              hsame row completionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionReadUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr completionRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, completionPkg, source.left⟩
  }
  exact ⟨cert, radiusReadUnary, orderReadUnary, completionReadUnary⟩

end BEDC.Derived.FormalBallUp
