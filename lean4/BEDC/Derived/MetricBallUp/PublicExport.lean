import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_public_export [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow transportedRadius
      radiusRead packageRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg →
      hsame transportedRadius radius →
        Cont transportedRadius positive radiusRead →
          Cont radiusRead replay packageRead →
            Cont member packageRead publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row dist ∨ hsame row center ∨
                        hsame row radius ∨ hsame row positive ∨ hsame row member ∨
                          hsame row packageRead ∨ hsame row publicRead ∨
                            Cont member packageRead publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                        hsame row publicRead)
                    hsame ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportedSame radiusRoute packageRoute publicRoute publicPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, radiusUnary, positiveUnary, memberUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameUnary, _positiveMemberRoute,
    _memberReplayRoute, _provenancePkg, _namePkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedRadius :=
    unary_transport radiusUnary (hsame_symm transportedSame)
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed transportedUnary positiveUnary radiusRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed radiusReadUnary replayUnary packageRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed memberUnary packageReadUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row dist ∨ hsame row center ∨ hsame row radius ∨
              hsame row positive ∨ hsame row member ∨ hsame row packageRead ∨
                hsame row publicRead ∨ Cont member packageRead publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg, source.left⟩
  }
  exact ⟨cert, publicReadUnary⟩

end BEDC.Derived.MetricBallUp
