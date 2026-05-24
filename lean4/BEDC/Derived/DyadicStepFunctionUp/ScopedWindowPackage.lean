import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicStepFunctionCarrier_scoped_window_package [AskSetup] [PackageSetup]
    {partitionS cellsS valuesS readsS refinementS endpointLedgerS ledgerS routeS
      provenanceS nameRowS partitionT cellsT valuesT readsT refinementT endpointLedgerT ledgerT
      routeT provenanceT nameRowT commonCell endpointReadS endpointReadT visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partitionS cellsS valuesS readsS refinementS endpointLedgerS
        ledgerS routeS provenanceS nameRowS bundle pkg ->
      DyadicStepFunctionCarrier partitionT cellsT valuesT readsT refinementT endpointLedgerT
          ledgerT routeT provenanceT nameRowT bundle pkg ->
        Cont cellsS cellsT commonCell ->
          Cont commonCell endpointLedgerS endpointReadS ->
            Cont commonCell endpointLedgerT endpointReadT ->
              Cont endpointReadS endpointReadT visibleRead ->
                PkgSig bundle visibleRead pkg ->
                  UnaryHistory commonCell ∧ UnaryHistory endpointReadS ∧
                    UnaryHistory endpointReadT ∧ UnaryHistory visibleRead ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row visibleRead ∧ UnaryHistory row)
                        (fun row : BHist => hsame row commonCell ∨ hsame row visibleRead)
                        (fun row : BHist =>
                          PkgSig bundle visibleRead pkg ∧ hsame row visibleRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrierS carrierT cellsCommon commonEndpointS commonEndpointT endpointVisible
    visiblePkg
  obtain ⟨_partitionSUnary, cellsSUnary, _valuesSUnary, _readsSUnary, _refinementSUnary,
    endpointLedgerSUnary, _ledgerSUnary, _routeSUnary, _provenanceSUnary, _nameRowSUnary,
    _partitionCellsValuesS, _valuesReadsRefinementS, _refinementEndpointLedgerS,
    _routeProvenanceNameRowS, _nameRowSPkg⟩ := carrierS
  obtain ⟨_partitionTUnary, cellsTUnary, _valuesTUnary, _readsTUnary, _refinementTUnary,
    endpointLedgerTUnary, _ledgerTUnary, _routeTUnary, _provenanceTUnary, _nameRowTUnary,
    _partitionCellsValuesT, _valuesReadsRefinementT, _refinementEndpointLedgerT,
    _routeProvenanceNameRowT, _nameRowTPkg⟩ := carrierT
  have commonCellUnary : UnaryHistory commonCell :=
    unary_cont_closed cellsSUnary cellsTUnary cellsCommon
  have endpointReadSUnary : UnaryHistory endpointReadS :=
    unary_cont_closed commonCellUnary endpointLedgerSUnary commonEndpointS
  have endpointReadTUnary : UnaryHistory endpointReadT :=
    unary_cont_closed commonCellUnary endpointLedgerTUnary commonEndpointT
  have visibleReadUnary : UnaryHistory visibleRead :=
    unary_cont_closed endpointReadSUnary endpointReadTUnary endpointVisible
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row visibleRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row commonCell ∨ hsame row visibleRead)
        (fun row : BHist => PkgSig bundle visibleRead pkg ∧ hsame row visibleRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro visibleRead ⟨hsame_refl visibleRead, visibleReadUnary⟩
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
        exact ⟨visiblePkg, source.left⟩
    }
  exact ⟨commonCellUnary, endpointReadSUnary, endpointReadTUnary, visibleReadUnary, cert⟩

end BEDC.Derived.DyadicStepFunctionUp
