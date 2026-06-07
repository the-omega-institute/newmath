import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SchurOrthogonalityCarrier [AskSetup] [PackageSetup]
    (group vec character pairing orthogonality transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory group ∧ UnaryHistory vec ∧ UnaryHistory character ∧
    UnaryHistory pairing ∧ UnaryHistory orthogonality ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont group vec pairing ∧ Cont character pairing orthogonality ∧
          Cont orthogonality transport replay ∧ Cont replay provenance localName ∧
            PkgSig bundle localName pkg

theorem SchurOrthogonalityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            SchurOrthogonalityCarrier group vec character pairing orthogonality transport
                replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            hsame row group ∨ hsame row vec ∨ hsame row character ∨ hsame row pairing ∨
              hsame row orthogonality ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨_groupUnary, _vecUnary, _characterUnary, _pairingUnary, _orthogonalityUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _groupVecPairing,
    _characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport localNameUnary (hsame_symm source.right), localNamePkg⟩
  }

end BEDC.Derived.SchurOrthogonalityUp
