import BEDC.Derived.CrossPerspectiveAlignmentUp.LocalityCellSoundness
import BEDC.Derived.CrossPerspectiveAlignmentUp.NameCertObligations

namespace BEDC.Derived.CrossPerspectiveAlignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CrossPerspectiveAlignmentCarrier_finite_multihist_coherence [AskSetup] [PackageSetup]
    {source target locality commitment multiHist transports routes provenance nameCert
      coherenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports routes
        provenance nameCert bundle pkg ->
      Cont multiHist transports coherenceRead ->
        PkgSig bundle coherenceRead pkg ->
          UnaryHistory multiHist ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
            UnaryHistory coherenceRead ∧ Cont multiHist transports coherenceRead ∧
              hsame nameCert source ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle coherenceRead pkg ∧
                  SemanticNameCert
                    (fun row : BHist =>
                      CrossPerspectiveAlignmentCarrier source target locality commitment multiHist
                        transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
                    (fun row : BHist =>
                      hsame row nameCert ∨ hsame row multiHist ∨ hsame row coherenceRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle coherenceRead pkg ∧
                        hsame row nameCert)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier multiHistTransportsRead coherencePkg
  have carrierPacket :
      CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports
        routes provenance nameCert bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _targetUnary, _localityUnary, _commitmentUnary, multiHistUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameCertUnary, nameCertSameSource,
    provenancePkg⟩ := carrier
  have coherenceUnary : UnaryHistory coherenceRead :=
    unary_cont_closed multiHistUnary transportsUnary multiHistTransportsRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports
            routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          hsame row nameCert ∨ hsame row multiHist ∨ hsame row coherenceRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle coherenceRead pkg ∧ hsame row nameCert)
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
        exact ⟨provenancePkg, coherencePkg, sourceRow.right⟩
    }
  exact
    ⟨multiHistUnary, transportsUnary, routesUnary, coherenceUnary, multiHistTransportsRead,
      nameCertSameSource, provenancePkg, coherencePkg, cert⟩

end BEDC.Derived.CrossPerspectiveAlignmentUp
