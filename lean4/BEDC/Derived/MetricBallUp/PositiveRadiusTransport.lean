import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricBallCarrier [AskSetup] [PackageSetup]
    (X dist center radius positive member transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory X ∧ UnaryHistory dist ∧ UnaryHistory center ∧ UnaryHistory radius ∧
    UnaryHistory positive ∧ UnaryHistory member ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont radius positive member ∧ Cont member transport replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg

theorem MetricBallCarrier_positive_radius_transport [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow transportedRadius
      radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg ->
      hsame transportedRadius radius ->
        Cont transportedRadius positive radiusRead ->
          PkgSig bundle radiusRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row transportedRadius ∨ hsame row radiusRead ∨
                    Cont transportedRadius positive radiusRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle radiusRead pkg ∧
                    hsame row radiusRead)
                hsame ∧
              UnaryHistory transportedRadius ∧ UnaryHistory radiusRead ∧
                Cont transportedRadius positive radiusRead ∧ PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportedSame positiveRoute radiusPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, radiusUnary, positiveUnary, _memberUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _namePkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedRadius :=
    unary_transport radiusUnary (hsame_symm transportedSame)
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed transportedUnary positiveUnary positiveRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row transportedRadius ∨ hsame row radiusRead ∨
              Cont transportedRadius positive radiusRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle radiusRead pkg ∧
              hsame row radiusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro radiusRead ⟨hsame_refl radiusRead, radiusReadUnary⟩
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
        have otherSame : hsame other radiusRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, radiusPkg, source.left⟩
  }
  exact ⟨cert, transportedUnary, radiusReadUnary, positiveRoute, radiusPkg⟩

end BEDC.Derived.MetricBallUp
