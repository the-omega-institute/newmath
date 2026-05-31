import BEDC.Derived.MetricBallUp.NameCertObligations

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_topology_handoff [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow topologyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg →
      Cont member replay topologyRead →
        PkgSig bundle topologyRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row topologyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row member ∨ hsame row replay ∨ Cont member replay topologyRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle topologyRead pkg ∧
                  hsame row topologyRead)
              hsame ∧
            UnaryHistory topologyRead ∧ Cont member replay topologyRead ∧
              PkgSig bundle topologyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier topologyRoute topologyPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, _radiusUnary, _positiveUnary, memberUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameRowUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _nameRowPkg⟩ := carrier
  have topologyUnary : UnaryHistory topologyRead :=
    unary_cont_closed memberUnary replayUnary topologyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row topologyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row member ∨ hsame row replay ∨ Cont member replay topologyRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle topologyRead pkg ∧
              hsame row topologyRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro topologyRead
        ⟨hsame_refl topologyRead, topologyUnary⟩
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
        have otherSame : hsame other topologyRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr topologyRoute)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, topologyPkg, source.left⟩
  }
  exact ⟨cert, topologyUnary, topologyRoute, topologyPkg⟩

end BEDC.Derived.MetricBallUp
