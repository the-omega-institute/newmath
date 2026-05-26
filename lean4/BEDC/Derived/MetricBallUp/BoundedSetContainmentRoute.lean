import BEDC.Derived.MetricBallUp.TopologyHandoff

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_boundedset_containment_route [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg →
      Cont member positive boundedRead →
        PkgSig bundle boundedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row member ∨ hsame row positive ∨ hsame row boundedRead ∨
                  Cont member positive boundedRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle boundedRead pkg ∧
                  hsame row boundedRead)
              hsame ∧
            UnaryHistory boundedRead ∧ Cont member positive boundedRead ∧
              PkgSig bundle boundedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundedRoute boundedPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, _radiusUnary, positiveUnary, memberUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameRowUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _nameRowPkg⟩ := carrier
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed memberUnary positiveUnary boundedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row member ∨ hsame row positive ∨ hsame row boundedRead ∨
              Cont member positive boundedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundedRead pkg ∧
              hsame row boundedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead
        ⟨hsame_refl boundedRead, boundedUnary⟩
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
        have otherSame : hsame other boundedRead :=
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
      exact ⟨provenancePkg, boundedPkg, source.left⟩
  }
  exact ⟨cert, boundedUnary, boundedRoute, boundedPkg⟩

end BEDC.Derived.MetricBallUp
