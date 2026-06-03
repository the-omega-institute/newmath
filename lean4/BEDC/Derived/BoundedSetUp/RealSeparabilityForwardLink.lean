import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_real_separability_forward_link [AskSetup] [PackageSetup]
    {X S c r B H C P N separabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S c r B H C P N bundle pkg ->
      Cont B C separabilityRead ->
        PkgSig bundle separabilityRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row separabilityRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row S ∨ hsame row c ∨ hsame row r ∨
                  hsame row B ∨ Cont B C separabilityRead)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle separabilityRead pkg ∧
                  hsame row separabilityRead)
              hsame ∧
            UnaryHistory separabilityRead ∧ Cont B C separabilityRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle separabilityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier ballReplaySeparability separabilityPkg
  obtain ⟨_xUnary, _sUnary, _centerUnary, _radiusUnary, ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have separabilityUnary : UnaryHistory separabilityRead :=
    unary_cont_closed ballUnary replayUnary ballReplaySeparability
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separabilityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row c ∨ hsame row r ∨
              hsame row B ∨ Cont B C separabilityRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle separabilityRead pkg ∧
              hsame row separabilityRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separabilityRead
          ⟨hsame_refl separabilityRead, separabilityUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ballReplaySeparability))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, separabilityPkg, source.left⟩
  }
  exact
    ⟨cert, separabilityUnary, ballReplaySeparability, provenancePkg, separabilityPkg⟩

end BEDC.Derived.BoundedSetUp
