import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_radius_ledger [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow radiusRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont center radius radiusRead ->
        Cont radiusRead ball ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row radius ∨ hsame row ball ∨ hsame row ledgerRead ∨
                    Cont radiusRead ball ledgerRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                    hsame row ledgerRead)
                hsame ∧
              UnaryHistory radius ∧ UnaryHistory radiusRead ∧ UnaryHistory ledgerRead ∧
                Cont center radius radiusRead ∧ Cont radiusRead ball ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier centerRadius radiusBallLedger ledgerPkg
  obtain ⟨_xUnary, _sUnary, centerUnary, radiusUnary, ballUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary radiusUnary centerRadius
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed radiusReadUnary ballUnary radiusBallLedger
  have sourceLedger :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row ball ∨ hsame row ledgerRead ∨
              Cont radiusRead ball ledgerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
              hsame row ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceLedger
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, ledgerPkg, source.left⟩
  }
  exact ⟨cert, radiusUnary, radiusReadUnary, ledgerReadUnary, centerRadius, radiusBallLedger⟩

end BEDC.Derived.BoundedSetUp
