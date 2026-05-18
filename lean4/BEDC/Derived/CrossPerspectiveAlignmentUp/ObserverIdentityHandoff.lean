import BEDC.Derived.CrossPerspectiveAlignmentUp.NameCertObligations

namespace BEDC.Derived.CrossPerspectiveAlignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CrossPerspectiveAlignmentCarrier_observer_identity_handoff [AskSetup] [PackageSetup]
    {source target locality commitment multiHist transports routes provenance nameCert
      identityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports routes
        provenance nameCert bundle pkg ->
      Cont target commitment identityRead ->
        PkgSig bundle identityRead pkg ->
          UnaryHistory target ∧ UnaryHistory commitment ∧ UnaryHistory identityRead ∧
            Cont target commitment identityRead ∧ hsame nameCert source ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle identityRead pkg ∧
                SemanticNameCert
                  (fun row : BHist =>
                    CrossPerspectiveAlignmentCarrier source target locality commitment multiHist
                      transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
                  (fun row : BHist =>
                    hsame row nameCert ∨ hsame row target ∨ hsame row identityRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle identityRead pkg ∧
                      hsame row nameCert)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier targetCommitmentRead identityPkg
  have carrierPacket :
      CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports
        routes provenance nameCert bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, targetUnary, _localityUnary, commitmentUnary, _multiHistUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, nameCertSameSource,
    provenancePkg⟩ := carrier
  have identityUnary : UnaryHistory identityRead :=
    unary_cont_closed targetUnary commitmentUnary targetCommitmentRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports
            routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          hsame row nameCert ∨ hsame row target ∨ hsame row identityRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle identityRead pkg ∧ hsame row nameCert)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameCert ⟨carrierPacket, hsame_refl nameCert⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same sourceRow
          exact ⟨sourceRow.left, hsame_trans (hsame_symm same) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inl sourceRow.right
      ledger_sound := by
        intro _row sourceRow
        exact ⟨provenancePkg, identityPkg, sourceRow.right⟩
    }
  exact
    ⟨targetUnary, commitmentUnary, identityUnary, targetCommitmentRead, nameCertSameSource,
      provenancePkg, identityPkg, cert⟩

end BEDC.Derived.CrossPerspectiveAlignmentUp
