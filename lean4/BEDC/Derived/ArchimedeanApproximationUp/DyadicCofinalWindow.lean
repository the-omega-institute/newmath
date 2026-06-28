import BEDC.Derived.ArchimedeanApproximationUp.TasteGate

namespace BEDC.Derived.ArchimedeanApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanApproximationCarrier_dyadic_cofinal_window [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName refinedBound refinedDyadic refinedTolerance refinedWindow refinedReadback
      refinedSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg →
      UnaryHistory refinedBound →
        UnaryHistory refinedDyadic →
          UnaryHistory refinedWindow →
            Cont refinedBound refinedDyadic refinedTolerance →
              Cont refinedTolerance refinedWindow refinedReadback →
                Cont refinedReadback sealRow refinedSealRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localName pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row refinedReadback ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row refinedBound ∨ hsame row refinedDyadic ∨
                              hsame row refinedTolerance ∨ hsame row refinedWindow ∨
                                hsame row refinedReadback ∨ hsame row sealRow)
                          (fun row : BHist =>
                            UnaryHistory row ∧
                              Cont refinedBound refinedDyadic refinedTolerance ∧
                                Cont refinedTolerance refinedWindow refinedReadback ∧
                                  Cont refinedReadback sealRow refinedSealRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                          hsame ∧ UnaryHistory refinedTolerance ∧
                        UnaryHistory refinedReadback ∧ UnaryHistory refinedSealRead := by
  -- BEDC touchpoint anchor: ArchimedeanApproximationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refinedBoundUnary refinedDyadicUnary refinedWindowUnary
    refinedBoundDyadic refinedToleranceWindow refinedReadbackSeal provenancePkg namePkg
  obtain ⟨_boundUnary, _rationalUnary, _dyadicUnary, _toleranceUnary, _windowUnary,
    _readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have refinedToleranceUnary : UnaryHistory refinedTolerance :=
    unary_cont_closed refinedBoundUnary refinedDyadicUnary refinedBoundDyadic
  have refinedReadbackUnary : UnaryHistory refinedReadback :=
    unary_cont_closed refinedToleranceUnary refinedWindowUnary refinedToleranceWindow
  have refinedSealReadUnary : UnaryHistory refinedSealRead :=
    unary_cont_closed refinedReadbackUnary sealUnary refinedReadbackSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedReadback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refinedBound ∨ hsame row refinedDyadic ∨
              hsame row refinedTolerance ∨ hsame row refinedWindow ∨
                hsame row refinedReadback ∨ hsame row sealRow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont refinedBound refinedDyadic refinedTolerance ∧
              Cont refinedTolerance refinedWindow refinedReadback ∧
                Cont refinedReadback sealRow refinedSealRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedReadback
          ⟨hsame_refl refinedReadback, refinedReadbackUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, refinedBoundDyadic, refinedToleranceWindow, refinedReadbackSeal,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, refinedToleranceUnary, refinedReadbackUnary, refinedSealReadUnary⟩

end BEDC.Derived.ArchimedeanApproximationUp
