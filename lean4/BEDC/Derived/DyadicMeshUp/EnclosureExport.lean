import BEDC.Derived.DyadicMeshUp

namespace BEDC.Derived.DyadicMeshUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicMeshPacket_refinement_enclosure_export [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert meshCell
      realBoundary terminalRead validatedRead enclosure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint meshCell ->
        Cont meshCell provenance realBoundary ->
          Cont realBoundary transport terminalRead ->
            Cont terminalRead refinement validatedRead ->
              Cont validatedRead nameCert enclosure ->
                PkgSig bundle meshCell pkg ->
                  PkgSig bundle realBoundary pkg ->
                    PkgSig bundle validatedRead pkg ->
                      PkgSig bundle enclosure pkg ->
                        UnaryHistory enclosure ∧ Cont validatedRead nameCert enclosure ∧
                          PkgSig bundle enclosure pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row enclosure ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row validatedRead ∨ hsame row enclosure)
                              (fun row : BHist =>
                                hsame row enclosure ∧ PkgSig bundle enclosure pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet intervalEndpointMesh meshProvenanceBoundary boundaryTransportTerminal
    terminalRefinementValidated validatedNameEnclosure _meshPkg _boundaryPkg _validatedPkg
    enclosurePkg
  rcases packet with
    ⟨_levelUnary, _cellUnary, intervalUnary, endpointUnary, _radiusUnary, _orderUnary,
      transportUnary, refinementUnary, provenanceUnary, nameCertUnary, _levelCellInterval,
      _intervalEndpointRadius, _provenancePkg⟩
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointMesh
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceBoundary
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed boundaryUnary transportUnary boundaryTransportTerminal
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed terminalUnary refinementUnary terminalRefinementValidated
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed validatedUnary nameCertUnary validatedNameEnclosure
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row enclosure ∧ UnaryHistory row)
        (fun row : BHist => hsame row validatedRead ∨ hsame row enclosure)
        (fun row : BHist => hsame row enclosure ∧ PkgSig bundle enclosure pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro enclosure ⟨hsame_refl enclosure, enclosureUnary⟩
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, enclosurePkg⟩
  }
  exact ⟨enclosureUnary, validatedNameEnclosure, enclosurePkg, cert⟩

end BEDC.Derived.DyadicMeshUp
