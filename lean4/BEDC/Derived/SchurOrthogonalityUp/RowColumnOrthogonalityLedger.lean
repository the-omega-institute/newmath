import BEDC.Derived.SchurOrthogonalityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurOrthogonalityRowColumnOrthogonalityLedger [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName
      rowRead columnRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      Cont pairing orthogonality rowRead → Cont rowRead replay columnRead →
        Cont columnRead localName consumer →
          SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist => hsame row rowRead ∨ hsame row columnRead ∨
              hsame row orthogonality ∨ hsame row localName ∨ hsame row consumer)
            (fun row : BHist => hsame row consumer ∧ PkgSig bundle localName pkg)
            hsame ∧ UnaryHistory rowRead ∧ UnaryHistory columnRead ∧
              UnaryHistory consumer := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier pairingOrthogonality rowReplay columnLocal
  obtain ⟨_groupUnary, _vecUnary, _characterUnary, pairingUnary, orthogonalityUnary,
    _transportUnary, replayUnary, _provenanceUnary, localNameUnary, _groupVecPairing,
    _characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    localNamePkg⟩ := carrier
  have rowUnary : UnaryHistory rowRead :=
    unary_cont_closed pairingUnary orthogonalityUnary pairingOrthogonality
  have columnUnary : UnaryHistory columnRead :=
    unary_cont_closed rowUnary replayUnary rowReplay
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed columnUnary localNameUnary columnLocal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist => hsame row rowRead ∨ hsame row columnRead ∨
          hsame row orthogonality ∨ hsame row localName ∨ hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle localName pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, localNamePkg⟩
  }
  exact ⟨cert, rowUnary, columnUnary, consumerUnary⟩

end BEDC.Derived.SchurOrthogonalityUp
