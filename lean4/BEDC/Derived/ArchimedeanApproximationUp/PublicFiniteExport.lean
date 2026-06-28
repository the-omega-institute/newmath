import BEDC.Derived.ArchimedeanApproximationUp.TasteGate

namespace BEDC.Derived.ArchimedeanApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanApproximationPublicFiniteExport [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg →
      Cont readback sealRow publicRead →
        PkgSig bundle provenance pkg →
          PkgSig bundle localName pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row publicRead ∨ hsame row readback ∨ hsame row sealRow) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
                    hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                      hsame row sealRow ∨ hsame row transportRow ∨ hsame row replayRow ∨
                        hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    ArchimedeanApproximationCarrier bound rational dyadic tolerance window
                      readback sealRow transportRow replayRow provenance localName bundle pkg ∧
                      Cont readback sealRow publicRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ArchimedeanApproximationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute provenancePkg namePkg
  have carrierWitness :
      ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg := carrier
  obtain ⟨_boundUnary, _rationalUnary, _dyadicUnary, _toleranceUnary, _windowUnary,
    readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackUnary sealUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row publicRead ∨ hsame row readback ∨ hsame row sealRow) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row transportRow ∨ hsame row replayRow ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback
                sealRow transportRow replayRow provenance localName bundle pkg ∧
                Cont readback sealRow publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨Or.inl (hsame_refl publicRead), publicUnary⟩
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
        have lift : forall {target : BHist}, hsame row target → hsame other target := by
          intro _target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl samePublic =>
              exact Or.inl (lift samePublic)
          | inr rest =>
              cases rest with
              | inl sameReadback =>
                  exact Or.inr (Or.inl (lift sameReadback))
              | inr sameSeal =>
                  exact Or.inr (Or.inr (lift sameSeal))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl samePublic =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr samePublic))))))))))
      | inr rest =>
          cases rest with
          | inl sameReadback =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameReadback)))))
          | inr sameSeal =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSeal))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierWitness, publicRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.ArchimedeanApproximationUp
