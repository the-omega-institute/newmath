import BEDC.Derived.ArchimedeanApproximationUp.TasteGate

namespace BEDC.Derived.ArchimedeanApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanApproximationCarrier_dyadic_upper_ladder [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName ladderRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont bound dyadic ladderRead ->
        Cont ladderRead tolerance toleranceRead ->
          Cont toleranceRead sealRow sealRead ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle localName pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row ladderRead ∨ hsame row toleranceRead ∨
                          hsame row sealRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
                        hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                          hsame row sealRow ∨ hsame row transportRow ∨
                            hsame row replayRow ∨ hsame row provenance ∨
                              hsame row localName ∨ hsame row ladderRead ∨
                                hsame row toleranceRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        ArchimedeanApproximationCarrier bound rational dyadic tolerance window
                          readback sealRow transportRow replayRow provenance localName bundle pkg ∧
                          Cont bound dyadic ladderRead ∧
                            Cont ladderRead tolerance toleranceRead ∧
                              Cont toleranceRead sealRow sealRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory ladderRead ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: ArchimedeanApproximationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ladderRoute toleranceRoute sealRoute provenancePkg namePkg
  have carrierWitness :
      ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg := carrier
  obtain ⟨boundUnary, _rationalUnary, dyadicUnary, toleranceUnary, _windowUnary,
    _readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have ladderUnary : UnaryHistory ladderRead :=
    unary_cont_closed boundUnary dyadicUnary ladderRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed ladderUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row ladderRead ∨ hsame row toleranceRead ∨ hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row transportRow ∨ hsame row replayRow ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row ladderRead ∨
                    hsame row toleranceRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback
                sealRow transportRow replayRow provenance localName bundle pkg ∧
                Cont bound dyadic ladderRead ∧ Cont ladderRead tolerance toleranceRead ∧
                  Cont toleranceRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ladderRead ⟨Or.inl (hsame_refl ladderRead), ladderUnary⟩
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
          | inl sameLadder =>
              exact Or.inl (lift sameLadder)
          | inr rest =>
              cases rest with
              | inl sameTolerance =>
                  exact Or.inr (Or.inl (lift sameTolerance))
              | inr sameSeal =>
                  exact Or.inr (Or.inr (lift sameSeal))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameLadder =>
          repeat (first | exact Or.inl sameLadder | apply Or.inr)
      | inr rest =>
          cases rest with
          | inl sameTolerance =>
              repeat (first | exact Or.inl sameTolerance | apply Or.inr)
          | inr sameSeal =>
              repeat (first | exact sameSeal | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierWitness, ladderRoute, toleranceRoute, sealRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, ladderUnary, toleranceReadUnary, sealReadUnary⟩

end BEDC.Derived.ArchimedeanApproximationUp
