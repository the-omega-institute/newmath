import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_namecert_ledger_nonescape [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead nameRow ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row ballRead ∨ hsame row ledgerRead ∨
                      Cont ballRead nameRow ledgerRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                      hsame row ledgerRead)
                  hsame ∧
                UnaryHistory memberRead ∧ UnaryHistory ballRead ∧ UnaryHistory ledgerRead ∧
                  Cont S center memberRead ∧ Cont memberRead radius ballRead ∧
                    Cont ballRead nameRow ledgerRead ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier subsetCenter memberRadius ballNameLedger ledgerPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    _replayUnary, _provenanceUnary, nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ballReadUnary nameUnary ballNameLedger
  have sourceLedger :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ballRead ∨ hsame row ledgerRead ∨ Cont ballRead nameRow ledgerRead)
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, ledgerPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, ledgerReadUnary, subsetCenter, memberRadius,
      ballNameLedger, ledgerPkg⟩

end BEDC.Derived.BoundedSetUp
