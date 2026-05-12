import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelRuffiniUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AbelRuffiniDerivedSeriesLedger_assoc_surface
    {galois sym commutator subgroup next : BHist} :
    UnaryHistory galois -> UnaryHistory sym -> UnaryHistory commutator ->
      Cont galois sym subgroup -> Cont subgroup commutator next ->
        ∃ tail : BHist, ∃ packed : BHist,
          Cont sym commutator tail ∧ Cont galois tail packed ∧ UnaryHistory subgroup ∧
            UnaryHistory tail ∧ UnaryHistory next ∧ UnaryHistory packed ∧ hsame next packed := by
  intro galoisUnary symUnary commutatorUnary subgroupRow nextRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisUnary symUnary subgroupRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  cases cont_assoc_left_exists subgroupRow nextRow with
  | intro tail repacked =>
      have tailUnary : UnaryHistory tail :=
        unary_cont_closed symUnary commutatorUnary repacked.left
      exact
        ⟨tail, next, repacked.left, repacked.right, subgroupUnary, tailUnary, nextUnary,
          nextUnary, hsame_refl next⟩

theorem AbelRuffiniPolynomialGaloisObligation_source_surface
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface : BHist} :
    UnaryHistory polynomial ->
      UnaryHistory base ->
        UnaryHistory splittingField ->
          UnaryHistory galoisRow ->
            Cont polynomial base coefficientLedger ->
              Cont splittingField galoisRow galoisLedger ->
                Cont coefficientLedger galoisLedger sourceSurface ->
                  UnaryHistory coefficientLedger ∧ UnaryHistory galoisLedger ∧
                    UnaryHistory sourceSurface ∧
                      hsame coefficientLedger (append polynomial base) ∧
                        hsame galoisLedger (append splittingField galoisRow) ∧
                          hsame sourceSurface (append coefficientLedger galoisLedger) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary
  intro coefficientRow galoisLedgerRow sourceSurfaceRow
  have coefficientUnary : UnaryHistory coefficientLedger :=
    unary_cont_closed polynomialUnary baseUnary coefficientRow
  have galoisLedgerUnary : UnaryHistory galoisLedger :=
    unary_cont_closed splittingFieldUnary galoisRowUnary galoisLedgerRow
  have sourceSurfaceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed coefficientUnary galoisLedgerUnary sourceSurfaceRow
  exact
    ⟨coefficientUnary,
      galoisLedgerUnary,
      sourceSurfaceUnary,
      coefficientRow,
      galoisLedgerRow,
      sourceSurfaceRow⟩

theorem AbelRuffiniDerivedSeriesLedger_finite_transport
    {galois s5 subgroup commutator next obstruction endpoint : BHist} :
    UnaryHistory galois -> UnaryHistory s5 -> UnaryHistory subgroup ->
      UnaryHistory commutator -> UnaryHistory obstruction ->
        Cont galois s5 subgroup -> Cont subgroup commutator next ->
          Cont next obstruction endpoint ->
            UnaryHistory next ∧ UnaryHistory endpoint ∧
              hsame subgroup (append galois s5) ∧ hsame next (append subgroup commutator) ∧
                hsame endpoint (append next obstruction) := by
  intro galoisUnary s5Unary subgroupUnary commutatorUnary obstructionUnary
  intro subgroupRow nextRow endpointRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed nextUnary obstructionUnary endpointRow
  exact ⟨nextUnary, endpointUnary, subgroupRow, nextRow, endpointRow⟩

theorem AbelRuffiniNonradicalBoundary_obstruction_surface
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface subgroup commutator next obstruction endpoint boundary : BHist} :
    UnaryHistory polynomial -> UnaryHistory base -> UnaryHistory splittingField ->
      UnaryHistory galoisRow -> UnaryHistory s5Row -> UnaryHistory commutator ->
        UnaryHistory obstruction -> Cont polynomial base coefficientLedger ->
          Cont splittingField galoisRow galoisLedger ->
            Cont coefficientLedger galoisLedger sourceSurface ->
              Cont galoisRow s5Row subgroup -> Cont subgroup commutator next ->
                Cont next obstruction endpoint -> Cont sourceSurface endpoint boundary ->
                  UnaryHistory sourceSurface ∧ UnaryHistory endpoint ∧ UnaryHistory boundary ∧
                    hsame sourceSurface (append coefficientLedger galoisLedger) ∧
                      hsame endpoint (append next obstruction) ∧
                        hsame boundary (append sourceSurface endpoint) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary s5RowUnary commutatorUnary
  intro obstructionUnary coefficientRow galoisLedgerRow sourceSurfaceRow subgroupRow nextRow
  intro endpointRow boundaryRow
  have sourceSurfaceData :=
    AbelRuffiniPolynomialGaloisObligation_source_surface (s5Row := s5Row) polynomialUnary
      baseUnary splittingFieldUnary galoisRowUnary coefficientRow galoisLedgerRow sourceSurfaceRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisRowUnary s5RowUnary subgroupRow
  have endpointData :=
    AbelRuffiniDerivedSeriesLedger_finite_transport galoisRowUnary s5RowUnary subgroupUnary
      commutatorUnary obstructionUnary subgroupRow nextRow endpointRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed sourceSurfaceData.right.right.left endpointData.right.left boundaryRow
  exact
    ⟨sourceSurfaceData.right.right.left, endpointData.right.left, boundaryUnary,
      sourceSurfaceData.right.right.right.right.right, endpointData.right.right.right.right,
      boundaryRow⟩

theorem AbelRuffiniNonradicalBoundary_obligation
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface commutator subgroup next obstruction boundary : BHist} :
    UnaryHistory polynomial -> UnaryHistory base -> UnaryHistory splittingField ->
      UnaryHistory galoisRow -> UnaryHistory s5Row -> UnaryHistory commutator ->
        UnaryHistory obstruction -> Cont polynomial base coefficientLedger ->
          Cont splittingField galoisRow galoisLedger ->
            Cont coefficientLedger galoisLedger sourceSurface ->
              Cont galoisRow s5Row subgroup -> Cont subgroup commutator next ->
                Cont next obstruction boundary ->
                  UnaryHistory sourceSurface ∧ UnaryHistory subgroup ∧ UnaryHistory next ∧
                    UnaryHistory boundary ∧
                      hsame sourceSurface (append coefficientLedger galoisLedger) ∧
                        hsame subgroup (append galoisRow s5Row) ∧
                          hsame next (append subgroup commutator) ∧
                            hsame boundary (append next obstruction) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary s5RowUnary
  intro commutatorUnary obstructionUnary coefficientRow galoisLedgerRow sourceSurfaceRow
  intro subgroupRow nextRow boundaryRow
  have coefficientUnary : UnaryHistory coefficientLedger :=
    unary_cont_closed polynomialUnary baseUnary coefficientRow
  have galoisLedgerUnary : UnaryHistory galoisLedger :=
    unary_cont_closed splittingFieldUnary galoisRowUnary galoisLedgerRow
  have sourceSurfaceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed coefficientUnary galoisLedgerUnary sourceSurfaceRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisRowUnary s5RowUnary subgroupRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed nextUnary obstructionUnary boundaryRow
  exact
    ⟨sourceSurfaceUnary, subgroupUnary, nextUnary, boundaryUnary, sourceSurfaceRow, subgroupRow,
      nextRow, boundaryRow⟩

theorem AbelRuffiniPublicCertificate_export
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger seed
      publicSurface : BHist} {derivedRows : List BHist} :
    UnaryHistory polynomial ->
      UnaryHistory base ->
        UnaryHistory splittingField ->
          UnaryHistory galoisRow ->
            UnaryHistory s5Row ->
              UnaryHistory seed ->
                (forall row : BHist, List.Mem row derivedRows -> UnaryHistory row) ->
                  Cont polynomial base coefficientLedger ->
                    Cont splittingField galoisRow galoisLedger ->
                      Cont coefficientLedger galoisLedger seed ->
                        Cont (List.foldl append seed derivedRows) s5Row publicSurface ->
                          UnaryHistory coefficientLedger ∧ UnaryHistory galoisLedger ∧
                            UnaryHistory (List.foldl append seed derivedRows) ∧
                              UnaryHistory publicSurface ∧
                                hsame publicSurface
                                  (append (List.foldl append seed derivedRows) s5Row) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary s5RowUnary seedUnary
  intro derivedUnary coefficientRow galoisLedgerRow seedRow publicSurfaceRow
  have coefficientUnary : UnaryHistory coefficientLedger :=
    unary_cont_closed polynomialUnary baseUnary coefficientRow
  have galoisLedgerUnary : UnaryHistory galoisLedger :=
    unary_cont_closed splittingFieldUnary galoisRowUnary galoisLedgerRow
  let rec foldUnaryClosed (current : BHist) :
      (rows : List BHist) ->
        UnaryHistory current ->
          (forall row : BHist, List.Mem row rows -> UnaryHistory row) ->
            UnaryHistory (List.foldl append current rows)
    | [], currentUnary, _ => currentUnary
    | head :: tail, currentUnary, rowsUnary =>
        have headUnary : UnaryHistory head :=
          rowsUnary head (List.Mem.head tail)
        have nextUnary : UnaryHistory (append current head) :=
          unary_cont_closed currentUnary headUnary rfl
        have tailUnary : forall row : BHist, List.Mem row tail -> UnaryHistory row := by
          intro row rowMem
          exact rowsUnary row (List.Mem.tail head rowMem)
        foldUnaryClosed (append current head) tail nextUnary tailUnary
  have foldUnary : UnaryHistory (List.foldl append seed derivedRows) := by
    exact foldUnaryClosed seed derivedRows seedUnary derivedUnary
  have publicSurfaceUnary : UnaryHistory publicSurface :=
    unary_cont_closed foldUnary s5RowUnary publicSurfaceRow
  exact ⟨coefficientUnary, galoisLedgerUnary, foldUnary, publicSurfaceUnary, publicSurfaceRow⟩

theorem AbelRuffiniPublicCertificateExport_namecert_surface
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface subgroup commutator next obstruction endpoint boundary publicSurface : BHist} :
    UnaryHistory polynomial -> UnaryHistory base -> UnaryHistory splittingField ->
      UnaryHistory galoisRow -> UnaryHistory s5Row -> UnaryHistory commutator ->
        UnaryHistory obstruction -> Cont polynomial base coefficientLedger ->
          Cont splittingField galoisRow galoisLedger ->
            Cont coefficientLedger galoisLedger sourceSurface ->
              Cont galoisRow s5Row subgroup -> Cont subgroup commutator next ->
                Cont next obstruction endpoint -> Cont sourceSurface endpoint boundary ->
                  Cont boundary s5Row publicSurface ->
                    UnaryHistory coefficientLedger ∧ UnaryHistory galoisLedger ∧
                      UnaryHistory sourceSurface ∧ UnaryHistory endpoint ∧ UnaryHistory boundary ∧
                        UnaryHistory publicSurface ∧
                          hsame sourceSurface (append coefficientLedger galoisLedger) ∧
                            hsame endpoint (append next obstruction) ∧
                              hsame boundary (append sourceSurface endpoint) ∧
                                hsame publicSurface (append boundary s5Row) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary s5RowUnary
  intro commutatorUnary obstructionUnary coefficientRow galoisLedgerRow sourceSurfaceRow
  intro subgroupRow nextRow endpointRow boundaryRow publicSurfaceRow
  have sourceData :=
    AbelRuffiniPolynomialGaloisObligation_source_surface (s5Row := s5Row) polynomialUnary baseUnary
      splittingFieldUnary galoisRowUnary coefficientRow galoisLedgerRow sourceSurfaceRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisRowUnary s5RowUnary subgroupRow
  have endpointData :=
    AbelRuffiniDerivedSeriesLedger_finite_transport galoisRowUnary s5RowUnary
      subgroupUnary commutatorUnary obstructionUnary subgroupRow nextRow endpointRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed sourceData.right.right.left endpointData.right.left boundaryRow
  have publicSurfaceUnary : UnaryHistory publicSurface :=
    unary_cont_closed boundaryUnary s5RowUnary publicSurfaceRow
  exact
    ⟨sourceData.left, sourceData.right.left, sourceData.right.right.left,
      endpointData.right.left, boundaryUnary, publicSurfaceUnary,
      sourceData.right.right.right.right.right, endpointData.right.right.right.right,
      boundaryRow, publicSurfaceRow⟩

theorem AbelRuffiniDerivedSeriesLedger_obstruction_endpoint_boundary
    {galois s5 subgroup commutator next obstruction endpoint boundary : BHist} :
    UnaryHistory galois -> UnaryHistory s5 -> UnaryHistory subgroup ->
      UnaryHistory commutator -> UnaryHistory obstruction -> Cont galois s5 subgroup ->
        Cont subgroup commutator next -> Cont next obstruction endpoint ->
          Cont subgroup endpoint boundary ->
            UnaryHistory next ∧ UnaryHistory endpoint ∧ UnaryHistory boundary ∧
              hsame subgroup (append galois s5) ∧ hsame next (append subgroup commutator) ∧
                hsame endpoint (append next obstruction) ∧
                  hsame boundary (append subgroup endpoint) := by
  intro galoisUnary s5Unary subgroupUnary commutatorUnary obstructionUnary
  intro subgroupRow nextRow endpointRow boundaryRow
  have finiteRows :=
    AbelRuffiniDerivedSeriesLedger_finite_transport galoisUnary s5Unary subgroupUnary
      commutatorUnary obstructionUnary subgroupRow nextRow endpointRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed subgroupUnary finiteRows.right.left boundaryRow
  exact
    ⟨finiteRows.left,
      finiteRows.right.left,
      boundaryUnary,
      finiteRows.right.right.left,
      finiteRows.right.right.right.left,
      finiteRows.right.right.right.right,
      boundaryRow⟩

theorem AbelRuffiniStandardRadicalTower_bridge_boundary
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface commutator subgroup next obstruction endpoint boundary publicSurface
      bridgeBoundary : BHist} :
    UnaryHistory polynomial -> UnaryHistory base -> UnaryHistory splittingField ->
      UnaryHistory galoisRow -> UnaryHistory s5Row -> UnaryHistory commutator ->
        UnaryHistory obstruction -> Cont polynomial base coefficientLedger ->
          Cont splittingField galoisRow galoisLedger ->
            Cont coefficientLedger galoisLedger sourceSurface ->
              Cont galoisRow s5Row subgroup -> Cont subgroup commutator next ->
                Cont next obstruction endpoint -> Cont sourceSurface endpoint boundary ->
                  Cont boundary s5Row publicSurface ->
                    Cont publicSurface s5Row bridgeBoundary ->
                      UnaryHistory sourceSurface ∧ UnaryHistory endpoint ∧
                        UnaryHistory boundary ∧ UnaryHistory publicSurface ∧
                          UnaryHistory bridgeBoundary ∧ hsame publicSurface (append boundary s5Row) ∧
                            hsame bridgeBoundary (append publicSurface s5Row) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary s5RowUnary
  intro commutatorUnary obstructionUnary coefficientRow galoisLedgerRow sourceSurfaceRow
  intro subgroupRow nextRow endpointRow boundaryRow publicSurfaceRow bridgeBoundaryRow
  have publicData :=
    AbelRuffiniPublicCertificateExport_namecert_surface polynomialUnary baseUnary
      splittingFieldUnary galoisRowUnary s5RowUnary commutatorUnary obstructionUnary
      coefficientRow galoisLedgerRow sourceSurfaceRow subgroupRow nextRow endpointRow
      boundaryRow publicSurfaceRow
  obtain ⟨_coefficientUnary, _galoisLedgerUnary, sourceSurfaceUnary, endpointUnary,
    boundaryUnary, publicSurfaceUnary, _sourceSurfaceSame, _endpointSame, _boundarySame,
    publicSurfaceSame⟩ := publicData
  have bridgeBoundaryUnary : UnaryHistory bridgeBoundary :=
    unary_cont_closed publicSurfaceUnary s5RowUnary bridgeBoundaryRow
  exact
    ⟨sourceSurfaceUnary, endpointUnary, boundaryUnary, publicSurfaceUnary, bridgeBoundaryUnary,
      publicSurfaceSame, bridgeBoundaryRow⟩

end BEDC.Derived.AbelRuffiniUp
