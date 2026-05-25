import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_finite_intersection_readiness [AskSetup] [PackageSetup]
    {X d c0 r0 rho0 m0 H0 C0 P0 N0 c1 r1 rho1 m1 H1 C1 P1 N1 intersectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X d c0 r0 rho0 m0 H0 C0 P0 N0 bundle pkg →
      MetricBallCarrier X d c1 r1 rho1 m1 H1 C1 P1 N1 bundle pkg →
        Cont m0 m1 intersectionRead →
          PkgSig bundle intersectionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row intersectionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row m0 ∨ hsame row m1 ∨ Cont m0 m1 intersectionRead)
                (fun row : BHist =>
                  PkgSig bundle P0 pkg ∧ PkgSig bundle P1 pkg ∧
                    PkgSig bundle intersectionRead pkg ∧ hsame row intersectionRead)
                hsame ∧ UnaryHistory intersectionRead ∧ Cont m0 m1 intersectionRead ∧
              PkgSig bundle intersectionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg PkgSig SemanticNameCert UnaryHistory hsame
  intro carrier0 carrier1 intersectionRoute intersectionPkg
  obtain ⟨_xUnary0, _distUnary0, _centerUnary0, _radiusUnary0, _positiveUnary0, m0Unary,
    _transportUnary0, _replayUnary0, _provenanceUnary0, _nameUnary0, _positiveMemberRoute0,
    _memberReplayRoute0, provenancePkg0, _namePkg0⟩ := carrier0
  obtain ⟨_xUnary1, _distUnary1, _centerUnary1, _radiusUnary1, _positiveUnary1, m1Unary,
    _transportUnary1, _replayUnary1, _provenanceUnary1, _nameUnary1, _positiveMemberRoute1,
    _memberReplayRoute1, provenancePkg1, _namePkg1⟩ := carrier1
  have intersectionUnary : UnaryHistory intersectionRead :=
    unary_cont_closed m0Unary m1Unary intersectionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row intersectionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row m0 ∨ hsame row m1 ∨ Cont m0 m1 intersectionRead)
          (fun row : BHist =>
            PkgSig bundle P0 pkg ∧ PkgSig bundle P1 pkg ∧
              PkgSig bundle intersectionRead pkg ∧ hsame row intersectionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro intersectionRead
        ⟨hsame_refl intersectionRead, intersectionUnary⟩
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
        have otherSame : hsame other intersectionRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr intersectionRoute)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg0, provenancePkg1, intersectionPkg, source.left⟩
  }
  exact ⟨cert, intersectionUnary, intersectionRoute, intersectionPkg⟩

end BEDC.Derived.MetricBallUp
