import BEDC.Derived.ArchimedeanApproximationUp.TasteGate

namespace BEDC.Derived.ArchimedeanApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanApproximationCarrier_kernel_scope [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont replayRow sealRow kernelRead ->
        PkgSig bundle provenance pkg ->
          PkgSig bundle localName pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row kernelRead ∨ hsame row sealRow ∨ hsame row replayRow) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
                    hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                      hsame row sealRow ∨ hsame row transportRow ∨
                        hsame row replayRow ∨ hsame row provenance ∨
                          hsame row localName ∨ hsame row kernelRead)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    ArchimedeanApproximationCarrier bound rational dyadic tolerance window
                      readback sealRow transportRow replayRow provenance localName bundle pkg ∧
                      Cont replayRow sealRow kernelRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory kernelRead := by
  -- BEDC touchpoint anchor: ArchimedeanApproximationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier replaySeal provenancePkg namePkg
  have carrierWitness :
      ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg := carrier
  obtain ⟨_boundUnary, _rationalUnary, _dyadicUnary, _toleranceUnary, _windowUnary,
    _readbackUnary, sealUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed replayUnary sealUnary replaySeal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row kernelRead ∨ hsame row sealRow ∨ hsame row replayRow) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row transportRow ∨ hsame row replayRow ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row kernelRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback
                sealRow transportRow replayRow provenance localName bundle pkg ∧
                Cont replayRow sealRow kernelRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro kernelRead ⟨Or.inl (hsame_refl kernelRead), kernelUnary⟩
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
        intro row other sameRows sourceRow
        have lift : forall {target : BHist}, hsame row target -> hsame other target := by
          intro _target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameKernel =>
              exact Or.inl (lift sameKernel)
          | inr rest =>
              cases rest with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (lift sameSeal))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (lift sameReplay))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameKernel =>
          repeat (first | exact sameKernel | apply Or.inr)
      | inr rest =>
          cases rest with
          | inl sameSeal =>
              repeat (first | exact Or.inl sameSeal | apply Or.inr)
          | inr sameReplay =>
              repeat (first | exact Or.inl sameReplay | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierWitness, replaySeal, provenancePkg, namePkg⟩
  }
  exact ⟨cert, kernelUnary⟩

end BEDC.Derived.ArchimedeanApproximationUp
