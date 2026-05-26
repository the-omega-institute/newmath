import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_scope_transport_package [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      commonCell endpointRead valueRead regRead realSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      Cont cells refinement commonCell ->
        Cont commonCell endpointLedger endpointRead ->
          Cont endpointRead values valueRead ->
            Cont ledger route regRead ->
              Cont regRead route realSeal ->
                Cont valueRead realSeal publicRead ->
                  PkgSig bundle publicRead pkg ->
                    UnaryHistory commonCell ∧ UnaryHistory endpointRead ∧
                      UnaryHistory valueRead ∧ UnaryHistory regRead ∧
                        UnaryHistory realSeal ∧ UnaryHistory publicRead ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist => hsame row commonCell ∨ hsame row publicRead)
                            (fun row : BHist =>
                              PkgSig bundle publicRead pkg ∧ hsame row publicRead)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier cellsRefinementCommon commonEndpoint endpointValue ledgerRoute regRouteReal
    valueRealPublic publicPkg
  obtain ⟨_partitionUnary, cellsUnary, valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, _refinementEndpointLedger,
    _routeProvenanceNameRow, _nameRowPkg⟩ := carrier
  have commonCellUnary : UnaryHistory commonCell :=
    unary_cont_closed cellsUnary refinementUnary cellsRefinementCommon
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed commonCellUnary endpointLedgerUnary commonEndpoint
  have valueReadUnary : UnaryHistory valueRead :=
    unary_cont_closed endpointReadUnary valuesUnary endpointValue
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary routeUnary regRouteReal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed valueReadUnary realSealUnary valueRealPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row commonCell ∨ hsame row publicRead)
        (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source.left⟩
    }
  exact
    ⟨commonCellUnary, endpointReadUnary, valueReadUnary, regReadUnary, realSealUnary,
      publicReadUnary, cert⟩

end BEDC.Derived.DyadicStepFunctionUp
