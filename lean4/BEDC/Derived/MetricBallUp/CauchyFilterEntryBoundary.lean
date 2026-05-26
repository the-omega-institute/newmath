import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_cauchy_filter_entry_boundary [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow filterRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg →
      Cont replay member filterRead →
        PkgSig bundle filterRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row filterRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row positive ∨ hsame row member ∨
                  hsame row filterRead ∨ Cont replay member filterRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle filterRead pkg ∧
                  hsame row filterRead)
              hsame ∧ UnaryHistory filterRead ∧ Cont replay member filterRead ∧
            PkgSig bundle filterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier filterRoute filterPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, _radiusUnary, _positiveUnary, memberUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameRowUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _nameRowPkg⟩ := carrier
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed replayUnary memberUnary filterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row filterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row positive ∨ hsame row member ∨
              hsame row filterRead ∨ Cont replay member filterRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle filterRead pkg ∧
              hsame row filterRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filterRead
        ⟨hsame_refl filterRead, filterUnary⟩
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
        have otherSame : hsame other filterRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, filterPkg, source.left⟩
  }
  exact ⟨cert, filterUnary, filterRoute, filterPkg⟩

end BEDC.Derived.MetricBallUp
