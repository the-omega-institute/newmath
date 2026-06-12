import BEDC.Derived.SchurOrthogonalityUp

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurOrthogonalityGroupAveragingLedger [AskSetup] [PackageSetup]
    {groupRow vectorRow characterRow pairingRow orthogonalityRow transport replay provenance
      localName averagingRead orthogonalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SchurOrthogonalityCarrier groupRow vectorRow characterRow pairingRow orthogonalityRow
        transport replay provenance localName bundle pkg →
      Cont groupRow characterRow averagingRead →
        Cont averagingRead orthogonalityRow orthogonalityRead →
          PkgSig bundle orthogonalityRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row orthogonalityRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row groupRow ∨ hsame row characterRow ∨ hsame row pairingRow ∨
                    hsame row orthogonalityRow ∨ hsame row averagingRead ∨
                      hsame row orthogonalityRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont groupRow characterRow averagingRead ∧
                    Cont averagingRead orthogonalityRow orthogonalityRead ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle orthogonalityRead pkg)
                hsame ∧
              UnaryHistory averagingRead ∧ UnaryHistory orthogonalityRead := by
  -- BEDC touchpoint anchor: SchurOrthogonalityCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier averagingRoute orthogonalityRoute orthogonalityPkg
  obtain ⟨groupUnary, _vectorUnary, characterUnary, _pairingUnary, orthogonalityUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _groupVecPairing,
    _characterPairingOrthogonality, _orthogonalityTransportReplay, _replayProvenanceName,
    localNamePkg⟩ := carrier
  have averagingUnary : UnaryHistory averagingRead :=
    unary_cont_closed groupUnary characterUnary averagingRoute
  have orthogonalityReadUnary : UnaryHistory orthogonalityRead :=
    unary_cont_closed averagingUnary orthogonalityUnary orthogonalityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orthogonalityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row characterRow ∨ hsame row pairingRow ∨
              hsame row orthogonalityRow ∨ hsame row averagingRead ∨
                hsame row orthogonalityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont groupRow characterRow averagingRead ∧
              Cont averagingRead orthogonalityRow orthogonalityRead ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle orthogonalityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro orthogonalityRead
          ⟨hsame_refl orthogonalityRead, orthogonalityReadUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, averagingRoute, orthogonalityRoute, localNamePkg, orthogonalityPkg⟩
  }
  exact ⟨cert, averagingUnary, orthogonalityReadUnary⟩

end BEDC.Derived.SchurOrthogonalityUp
