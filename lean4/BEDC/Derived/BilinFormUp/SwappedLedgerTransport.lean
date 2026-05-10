import BEDC.Derived.BilinFormUp

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BilinFormBHistObligationSurface_swapped_ledger_transport
    {left right scalar additive endpoint scalarLedger ledger swappedEndpoint swappedScalarLedger
      swappedLedger transportedLedger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      Cont right left swappedEndpoint ->
        Cont swappedEndpoint scalar swappedScalarLedger ->
          Cont swappedScalarLedger additive swappedLedger ->
            hsame swappedLedger transportedLedger ->
              BilinFormBHistObligationSurface right left scalar additive swappedEndpoint
                  swappedScalarLedger transportedLedger ∧
                hsame ledger transportedLedger := by
  intro surface swappedEndpointRow swappedScalarLedgerRow swappedLedgerRow sameTransported
  have swappedRows :=
    BilinFormBHistObligationSurface_symmetry_antisymmetry_obligations surface
      swappedEndpointRow swappedScalarLedgerRow swappedLedgerRow
  have transportedLedgerRow : Cont swappedScalarLedger additive transportedLedger :=
    cont_result_hsame_transport swappedLedgerRow sameTransported
  have transportedRows :=
    BilinFormBHistObligationSurface_symmetry_antisymmetry_obligations surface
      swappedEndpointRow swappedScalarLedgerRow transportedLedgerRow
  exact And.intro transportedRows.left
    (hsame_trans swappedRows.right.right.right sameTransported)

end BEDC.Derived.BilinFormUp
