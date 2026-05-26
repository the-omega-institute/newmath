import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_refinement_obligations [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow topologyRead
      boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg →
      Cont member positive topologyRead →
        Cont topologyRead member boundedRead →
          PkgSig bundle topologyRead pkg →
            PkgSig bundle boundedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row member ∨ hsame row topologyRead ∨ hsame row boundedRead ∨
                      Cont member positive topologyRead ∨ Cont topologyRead member boundedRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundedRead pkg ∧
                      hsame row boundedRead)
                  hsame ∧
                UnaryHistory topologyRead ∧ UnaryHistory boundedRead ∧
                  Cont member positive topologyRead ∧ Cont topologyRead member boundedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier topologyRoute boundedRoute _topologyPkg boundedPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, _radiusUnary, positiveUnary, memberUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameRowUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _nameRowPkg⟩ := carrier
  have topologyUnary : UnaryHistory topologyRead :=
    unary_cont_closed memberUnary positiveUnary topologyRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed topologyUnary memberUnary boundedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row member ∨ hsame row topologyRead ∨ hsame row boundedRead ∨
              Cont member positive topologyRead ∨ Cont topologyRead member boundedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundedRead pkg ∧
              hsame row boundedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead ⟨hsame_refl boundedRead, boundedUnary⟩
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
  exact ⟨cert, topologyUnary, boundedUnary, topologyRoute, boundedRoute⟩

end BEDC.Derived.MetricBallUp
