import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_obligation_transport_package [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow transportedRadius
      radiusRead packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg →
      hsame transportedRadius radius →
        Cont transportedRadius positive radiusRead →
          Cont radiusRead replay packageRead →
            PkgSig bundle packageRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row member ∨ hsame row radiusRead ∨
                      Cont radiusRead replay packageRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle packageRead pkg ∧
                      hsame row packageRead)
                  hsame ∧
                UnaryHistory transportedRadius ∧ UnaryHistory radiusRead ∧
                  UnaryHistory packageRead ∧ Cont transportedRadius positive radiusRead ∧
                    Cont radiusRead replay packageRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier transportedSame positiveRoute replayPackage packagePkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, radiusUnary, positiveUnary, _memberUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _namePkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedRadius :=
    unary_transport radiusUnary (hsame_symm transportedSame)
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed transportedUnary positiveUnary positiveRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed radiusReadUnary replayUnary replayPackage
  have sourcePackage :
      (fun row : BHist => hsame row packageRead ∧ UnaryHistory row) packageRead := by
    exact ⟨hsame_refl packageRead, packageReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row member ∨ hsame row radiusRead ∨
              Cont radiusRead replay packageRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle packageRead pkg ∧
              hsame row packageRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro packageRead sourcePackage
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
      exact Or.inr (Or.inr (Or.inr replayPackage))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, packagePkg, source.left⟩
  }
  exact
    ⟨cert, transportedUnary, radiusReadUnary, packageReadUnary, positiveRoute,
      replayPackage⟩

end BEDC.Derived.MetricBallUp
