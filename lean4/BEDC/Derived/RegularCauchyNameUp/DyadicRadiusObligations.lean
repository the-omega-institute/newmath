import BEDC.Derived.RegularCauchyNameUp

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyNameCarrier_dyadic_radius_obligations [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint radiusRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation radiusRead ->
        Cont radiusRead radius sealRead ->
          PkgSig bundle endpoint pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row schedule ∨ hsame row observation ∨ hsame row radius ∨
                    hsame row radiusRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont schedule observation radiusRead ∧
                    Cont radiusRead radius sealRead ∧ PkgSig bundle endpoint pkg)
                hsame ∧ UnaryHistory radiusRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier scheduleObservationRead radiusReadRadiusSeal endpointPkg
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, _scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, _carrierEndpointPkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed radiusReadUnary radiusUnary radiusReadRadiusSeal
  refine ⟨?_, radiusReadUnary, sealReadUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealReadUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _row' sameRows
    exact hsame_symm sameRows
  · intro _row _row' _row'' sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _row' sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
  · intro _row sourceRow
    exact ⟨sourceRow.right, scheduleObservationRead, radiusReadRadiusSeal, endpointPkg⟩

end BEDC.Derived.RegularCauchyNameUp
