import BEDC.Derived.SchurOrthogonalityUp.RowColumnOrthogonalityLedger

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurOrthogonalityScopedDependencyPackage [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName rowRead
      columnRead averagingRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      Cont pairing orthogonality rowRead →
        Cont rowRead replay columnRead →
          Cont group character averagingRead →
            Cont averagingRead orthogonality consumerRead →
              PkgSig bundle consumerRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row group ∨ hsame row vec ∨ hsame row character ∨
                        hsame row pairing ∨ hsame row orthogonality ∨ hsame row localName ∨
                          hsame row consumerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont group vec pairing ∧
                        Cont character pairing orthogonality ∧ PkgSig bundle localName pkg ∧
                          PkgSig bundle consumerRead pkg)
                    hsame ∧
                  UnaryHistory rowRead ∧ UnaryHistory columnRead ∧
                    UnaryHistory averagingRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier pairingOrthogonality rowReplay groupCharacter averagingOrthogonality
    consumerPkg
  obtain ⟨groupUnary, vecUnary, characterUnary, pairingUnary, orthogonalityUnary,
    _transportUnary, replayUnary, _provenanceUnary, localNameUnary, groupVecPairing,
    characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    localNamePkg⟩ := carrier
  have rowUnary : UnaryHistory rowRead :=
    unary_cont_closed pairingUnary orthogonalityUnary pairingOrthogonality
  have columnUnary : UnaryHistory columnRead :=
    unary_cont_closed rowUnary replayUnary rowReplay
  have averagingUnary : UnaryHistory averagingRead :=
    unary_cont_closed groupUnary characterUnary groupCharacter
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed averagingUnary orthogonalityUnary averagingOrthogonality
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row group ∨ hsame row vec ∨ hsame row character ∨ hsame row pairing ∨
              hsame row orthogonality ∨ hsame row localName ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont group vec pairing ∧
              Cont character pairing orthogonality ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, groupVecPairing, characterPairingOrthogonality, localNamePkg,
          consumerPkg⟩
  }
  exact ⟨cert, rowUnary, columnUnary, averagingUnary, consumerUnary⟩

end BEDC.Derived.SchurOrthogonalityUp
