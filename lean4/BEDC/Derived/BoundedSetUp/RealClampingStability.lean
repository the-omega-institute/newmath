import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_real_clamping_stability [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow radiusRead clampedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont center radius radiusRead ->
        Cont radiusRead ball clampedRead ->
          PkgSig bundle clampedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row clampedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row radius ∨ hsame row ball ∨ hsame row radiusRead ∨
                    hsame row clampedRead ∨ Cont center radius radiusRead ∨
                      Cont radiusRead ball clampedRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle clampedRead pkg ∧
                    hsame row clampedRead)
                hsame ∧
              UnaryHistory radiusRead ∧ UnaryHistory clampedRead ∧
                Cont center radius radiusRead ∧ Cont radiusRead ball clampedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle clampedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier radiusRoute clampedRoute clampedPkg
  obtain ⟨_xUnary, _sUnary, centerUnary, radiusUnary, ballUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary radiusUnary radiusRoute
  have clampedUnary : UnaryHistory clampedRead :=
    unary_cont_closed radiusReadUnary ballUnary clampedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row clampedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row ball ∨ hsame row radiusRead ∨
              hsame row clampedRead ∨ Cont center radius radiusRead ∨
                Cont radiusRead ball clampedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle clampedRead pkg ∧
              hsame row clampedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro clampedRead
        ⟨hsame_refl clampedRead, clampedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, clampedPkg, source.left⟩
  }
  exact
    ⟨cert, radiusReadUnary, clampedUnary, radiusRoute, clampedRoute, provenancePkg,
      clampedPkg⟩

end BEDC.Derived.BoundedSetUp
