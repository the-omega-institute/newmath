import BEDC.Derived.CausalCommitmentUp

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CausalCommitmentForwardGapCarrier_transport [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      observed' regularity' gap' forward' locality' transport' continuation' provenance'
      localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      hsame observed observed' ->
      hsame regularity regularity' ->
      hsame gap gap' ->
      hsame forward forward' ->
      hsame locality locality' ->
      hsame transport transport' ->
      hsame continuation continuation' ->
      hsame provenance provenance' ->
      hsame localCert localCert' ->
      PkgSig bundle localCert' pkg ->
        CausalCommitmentForwardGapCarrier observed' regularity' gap' forward' locality'
          transport' continuation' provenance' localCert' bundle pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier sameObserved sameRegularity sameGap sameForward sameLocality sameTransport
    sameContinuation sameProvenance sameLocalCert localCertPkg'
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  exact
    ⟨CausalCommitmentCarrier_transport baseCarrier sameObserved sameRegularity sameGap
        sameForward sameTransport sameContinuation sameProvenance sameLocalCert
        localCertPkg',
      unary_transport localityUnary sameLocality,
      cont_hsame_transport sameForward sameLocality sameLocalCert forwardLocalityLocalCert⟩

theorem CausalCommitmentLedgerNonescape [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
      Cont routeRead locality ledgerRead ->
      PkgSig bundle ledgerRead pkg ->
        SemanticNameCert
          (fun row : BHist =>
            CausalCommitmentForwardGapCarrier observed regularity gap forward locality
              transport continuation provenance localCert bundle pkg ∧ hsame row ledgerRead)
          (fun row : BHist =>
            Cont observed regularity gap ∧ Cont gap forward continuation ∧
              Cont forward locality localCert ∧ Cont continuation localCert routeRead ∧
                Cont routeRead locality ledgerRead ∧ hsame row ledgerRead)
          (fun row : BHist =>
            PkgSig bundle localCert pkg ∧ PkgSig bundle ledgerRead pkg ∧
              hsame row ledgerRead)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier continuationLocalCertRoute routeLocalityLedger ledgerPkg
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have forwardLocalityLocalCert : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  constructor
  · constructor
    · exact Exists.intro ledgerRead (And.intro carrierWitness (hsame_refl ledgerRead))
    · intro row _source
      exact hsame_refl row
    · intro _row _row' sameRows
      exact hsame_symm sameRows
    · intro _row _row' _row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _row' sameRows sourceRow
      exact
        ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
  · intro _row sourceRow
    exact
      ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityLocalCert,
        continuationLocalCertRoute, routeLocalityLedger, sourceRow.right⟩
  · intro _row sourceRow
    exact ⟨localCertPkg, ledgerPkg, sourceRow.right⟩

end BEDC.Derived.CausalCommitmentUp
