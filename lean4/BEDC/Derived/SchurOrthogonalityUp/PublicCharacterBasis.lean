import BEDC.Derived.SchurOrthogonalityUp.ScopedDependencyPackage

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurOrthogonalityPublicCharacterBasis [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      Cont orthogonality localName publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row group ∨ hsame row vec ∨ hsame row character ∨
                  hsame row pairing ∨ hsame row orthogonality ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont group vec pairing ∧
                  Cont character pairing orthogonality ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier publicRoute publicPkg
  obtain ⟨groupUnary, vecUnary, characterUnary, pairingUnary, orthogonalityUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, groupVecPairing,
    characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    _localNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed orthogonalityUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row group ∨ hsame row vec ∨ hsame row character ∨ hsame row pairing ∨
              hsame row orthogonality ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont group vec pairing ∧
              Cont character pairing orthogonality ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, groupVecPairing, characterPairingOrthogonality, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.SchurOrthogonalityUp
