import BEDC.Derived.SchurOrthogonalityUp

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurOrthogonalityCharacterPairingRoute [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName pairingRead
      orthogonalityRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      Cont character pairing pairingRead →
        Cont pairingRead orthogonality orthogonalityRead →
          Cont orthogonalityRead localName exportRead →
            PkgSig bundle exportRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row group ∨ hsame row vec ∨ hsame row character ∨
                      hsame row pairing ∨ hsame row orthogonality ∨ hsame row pairingRead ∨
                        hsame row orthogonalityRead ∨ hsame row exportRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont character pairing pairingRead ∧
                      Cont pairingRead orthogonality orthogonalityRead ∧
                        Cont orthogonalityRead localName exportRead ∧
                          PkgSig bundle exportRead pkg)
                  hsame ∧
                UnaryHistory pairingRead ∧ UnaryHistory orthogonalityRead ∧
                  UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier pairingRoute orthogonalityRoute exportRoute exportPkg
  obtain ⟨_groupUnary, _vecUnary, characterUnary, pairingUnary, orthogonalityUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _groupVecPairing,
    _characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    _localNamePkg⟩ := carrier
  have pairingReadUnary : UnaryHistory pairingRead :=
    unary_cont_closed characterUnary pairingUnary pairingRoute
  have orthogonalityReadUnary : UnaryHistory orthogonalityRead :=
    unary_cont_closed pairingReadUnary orthogonalityUnary orthogonalityRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed orthogonalityReadUnary localNameUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row group ∨ hsame row vec ∨ hsame row character ∨ hsame row pairing ∨
              hsame row orthogonality ∨ hsame row pairingRead ∨
                hsame row orthogonalityRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont character pairing pairingRead ∧
              Cont pairingRead orthogonality orthogonalityRead ∧
                Cont orthogonalityRead localName exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pairingRoute, orthogonalityRoute, exportRoute, exportPkg⟩
  }
  exact ⟨cert, pairingReadUnary, orthogonalityReadUnary, exportReadUnary⟩

theorem SchurOrthogonalityCharacterPairingRoute_withLocalNameCert [AskSetup] [PackageSetup]
    {group vec character pairing orthogonality transport replay provenance localName pairingRead
      orthogonalityRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier group vec character pairing orthogonality transport replay
        provenance localName bundle pkg →
      Cont character pairing pairingRead →
        Cont pairingRead orthogonality orthogonalityRead →
          Cont orthogonalityRead localName exportRead →
            PkgSig bundle exportRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    SchurOrthogonalityCarrier group vec character pairing orthogonality transport
                        replay provenance localName bundle pkg ∧ hsame row localName)
                  (fun row : BHist =>
                    hsame row group ∨ hsame row vec ∨ hsame row character ∨
                      hsame row pairing ∨ hsame row orthogonality ∨ hsame row localName)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
                  hsame ∧
                SemanticNameCert
                  (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row group ∨ hsame row vec ∨ hsame row character ∨
                      hsame row pairing ∨ hsame row orthogonality ∨ hsame row pairingRead ∨
                        hsame row orthogonalityRead ∨ hsame row exportRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont character pairing pairingRead ∧
                      Cont pairingRead orthogonality orthogonalityRead ∧
                        Cont orthogonalityRead localName exportRead ∧
                          PkgSig bundle exportRead pkg)
                  hsame ∧
                UnaryHistory pairingRead ∧ UnaryHistory orthogonalityRead ∧
                  UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier SemanticNameCert Cont PkgSig
  intro carrier pairingRoute orthogonalityRoute exportRoute exportPkg
  have localCert :=
    SchurOrthogonalityCarrier_namecert_obligations carrier
  have exportedRoute :=
    SchurOrthogonalityCharacterPairingRoute carrier pairingRoute orthogonalityRoute exportRoute
      exportPkg
  exact
    ⟨localCert, exportedRoute.1, exportedRoute.2.1, exportedRoute.2.2.1,
      exportedRoute.2.2.2⟩

end BEDC.Derived.SchurOrthogonalityUp
