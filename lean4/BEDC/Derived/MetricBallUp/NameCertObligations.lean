import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row member ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row positive ∨ hsame row member ∨
              Cont radius positive member ∨ Cont member transport replay)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧ hsame row member)
          hsame ∧
        UnaryHistory member ∧ Cont radius positive member ∧ Cont member transport replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_xUnary, _distUnary, _centerUnary, _radiusUnary, _positiveUnary, memberUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameRowUnary, positiveMemberRoute,
    memberReplayRoute, provenancePkg, nameRowPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row member ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row positive ∨ hsame row member ∨
              Cont radius positive member ∨ Cont member transport replay)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧ hsame row member)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro member ⟨hsame_refl member, memberUnary⟩
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
        intro row other sameRows source
        have otherSame : hsame other member :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, nameRowPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, positiveMemberRoute, memberReplayRoute, provenancePkg, nameRowPkg⟩

end BEDC.Derived.MetricBallUp
