import BEDC.Derived.SchurOrthogonalityUp

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurOrthogonalityCharacterInnerProduct [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName pairingRead
      orthogonalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      Cont group character pairingRead →
        Cont pairingRead pairing orthogonalityRead →
          PkgSig bundle orthogonalityRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row group ∨ hsame row vec ∨ hsame row character ∨
                    hsame row pairing ∨ hsame row pairingRead ∨
                      hsame row orthogonalityRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row group ∨ hsame row vec ∨ hsame row character ∨
                    hsame row pairing ∨ hsame row pairingRead ∨ hsame row orthogonality ∨
                      hsame row orthogonalityRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont group character pairingRead ∧
                    Cont pairingRead pairing orthogonalityRead ∧
                      PkgSig bundle orthogonalityRead pkg)
                hsame ∧
              UnaryHistory pairingRead ∧ UnaryHistory orthogonalityRead := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier groupCharacterRead pairingOrthogonalityRead orthogonalityReadPkg
  obtain ⟨groupUnary, vecUnary, characterUnary, pairingUnary, orthogonalityUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _groupVecPairing,
    _characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    _localNamePkg⟩ := carrier
  have pairingReadUnary : UnaryHistory pairingRead :=
    unary_cont_closed groupUnary characterUnary groupCharacterRead
  have orthogonalityReadUnary : UnaryHistory orthogonalityRead :=
    unary_cont_closed pairingReadUnary pairingUnary pairingOrthogonalityRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row group ∨ hsame row vec ∨ hsame row character ∨ hsame row pairing ∨
              hsame row pairingRead ∨ hsame row orthogonalityRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row group ∨ hsame row vec ∨ hsame row character ∨ hsame row pairing ∨
              hsame row pairingRead ∨ hsame row orthogonality ∨ hsame row orthogonalityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont group character pairingRead ∧
              Cont pairingRead pairing orthogonalityRead ∧
                PkgSig bundle orthogonalityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro orthogonalityRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl orthogonalityRead))))),
            orthogonalityReadUnary⟩
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
        constructor
        · cases source.left with
          | inl sameGroup =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameGroup)
          | inr rest =>
              cases rest with
              | inl sameVec =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameVec))
              | inr rest =>
                  cases rest with
                  | inl sameCharacter =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameCharacter)))
                  | inr rest =>
                      cases rest with
                      | inl samePairing =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) samePairing))))
                      | inr rest =>
                          cases rest with
                          | inl samePairingRead =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows)
                                            samePairingRead)))))
                          | inr sameOrthogonalityRead =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm sameRows)
                                            sameOrthogonalityRead)))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameGroup =>
          exact Or.inl sameGroup
      | inr rest =>
          cases rest with
          | inl sameVec =>
              exact Or.inr (Or.inl sameVec)
          | inr rest =>
              cases rest with
              | inl sameCharacter =>
                  exact Or.inr (Or.inr (Or.inl sameCharacter))
              | inr rest =>
                  cases rest with
                  | inl samePairing =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl samePairing)))
                  | inr rest =>
                      cases rest with
                      | inl samePairingRead =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl samePairingRead))))
                      | inr sameOrthogonalityRead =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr sameOrthogonalityRead)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, groupCharacterRead, pairingOrthogonalityRead, orthogonalityReadPkg⟩
  }
  exact ⟨cert, pairingReadUnary, orthogonalityReadUnary⟩

end BEDC.Derived.SchurOrthogonalityUp
