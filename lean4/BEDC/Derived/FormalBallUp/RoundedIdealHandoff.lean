import BEDC.Derived.FormalBallUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_rounded_ideal_handoff [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead roundedRead cauchyRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont radiusRead W roundedRead ->
          Cont roundedRead C cauchyRead ->
            Cont cauchyRead H uniformRead ->
              PkgSig bundle uniformRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row radiusRead ∨ hsame row roundedRead ∨
                            hsame row cauchyRead ∨ hsame row uniformRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R D radiusRead ∧
                        Cont radiusRead W roundedRead ∧ Cont roundedRead C cauchyRead ∧
                          Cont cauchyRead H uniformRead ∧ PkgSig bundle uniformRead pkg)
                    hsame ∧
                  UnaryHistory radiusRead ∧ UnaryHistory roundedRead ∧
                    UnaryHistory cauchyRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusRoute roundedRoute cauchyRoute uniformRoute uniformPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, windowUnary, transportUnary, replayUnary,
    _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindow, _transportReplay,
    _provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have roundedReadUnary : UnaryHistory roundedRead :=
    unary_cont_closed radiusReadUnary windowUnary roundedRoute
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed roundedReadUnary replayUnary cauchyRoute
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed cauchyReadUnary transportUnary uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row D ∨ hsame row W ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row radiusRead ∨ hsame row roundedRead ∨ hsame row cauchyRead ∨
                  hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R D radiusRead ∧
              Cont radiusRead W roundedRead ∧ Cont roundedRead C cauchyRead ∧
                Cont cauchyRead H uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformReadUnary⟩
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
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, radiusRoute, roundedRoute, cauchyRoute, uniformRoute, uniformPkg⟩
  }
  exact ⟨cert, radiusReadUnary, roundedReadUnary, cauchyReadUnary, uniformReadUnary⟩

end BEDC.Derived.FormalBallUp
