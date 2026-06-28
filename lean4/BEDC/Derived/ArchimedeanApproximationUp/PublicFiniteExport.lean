import BEDC.Derived.ArchimedeanApproximationUp.TasteGate

namespace BEDC.Derived.ArchimedeanApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace PublicFiniteExport

theorem ArchimedeanApproximationCarrier_public_finite_export [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg ->
      Cont bound dyadic tolerance ->
        Cont tolerance window readback ->
          Cont readback sealRow realRead ->
            Cont realRead replayRow publicRead ->
              PkgSig bundle provenance pkg ->
                PkgSig bundle localName pkg ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
                            hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                              hsame row sealRow ∨ hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont bound dyadic tolerance ∧
                            Cont tolerance window readback ∧ Cont readback sealRow realRead ∧
                              Cont realRead replayRow publicRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                                  PkgSig bundle publicRead pkg)
                        hsame ∧ UnaryHistory realRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ArchimedeanApproximationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundDyadic toleranceWindow readbackSeal realPublic provenancePkg namePkg publicPkg
  obtain ⟨boundUnary, _rationalUnary, dyadicUnary, _toleranceUnary, windowUnary,
    _readbackUnary, sealUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed boundUnary dyadicUnary boundDyadic
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary windowUnary toleranceWindow
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed realReadUnary replayUnary realPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bound dyadic tolerance ∧
              Cont tolerance window readback ∧ Cont readback sealRow realRead ∧
                Cont realRead replayRow publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, boundDyadic, toleranceWindow, readbackSeal, realPublic,
          provenancePkg, namePkg, publicPkg⟩
  }
  exact ⟨cert, realReadUnary, publicReadUnary⟩

end PublicFiniteExport

end BEDC.Derived.ArchimedeanApproximationUp
