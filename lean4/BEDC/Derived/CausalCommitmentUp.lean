import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.CausalCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def CausalCommitmentCarrier [AskSetup] [PackageSetup]
    (observed regularity gap forward transport continuation provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
    UnaryHistory forward ∧ UnaryHistory transport ∧ UnaryHistory continuation ∧
      UnaryHistory provenance ∧ UnaryHistory localCert ∧ Cont observed regularity gap ∧
        Cont gap forward continuation ∧ Cont transport continuation provenance ∧
          PkgSig bundle localCert pkg

theorem CausalCommitmentCarrier_gap_socket [AskSetup] [PackageSetup]
    {observed regularity gap forward transport continuation provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentCarrier observed regularity gap forward transport continuation provenance
        localCert bundle pkg ->
      UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
        Cont observed regularity gap ∧
          SemanticNameCert
            (fun row : BHist =>
              CausalCommitmentCarrier observed regularity gap forward transport continuation
                provenance localCert bundle pkg ∧ hsame row localCert)
            (fun row : BHist =>
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                hsame row localCert)
            (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
            hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨observedUnary, regularityUnary, gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CausalCommitmentCarrier observed regularity gap forward transport continuation
            provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          Cont observed regularity gap ∧ Cont gap forward continuation ∧
            hsame row localCert)
        (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localCert (And.intro carrierWitness (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨observedRegularityGap, gapForwardContinuation, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨localCertPkg, sourceRow.right⟩
  }
  exact ⟨observedUnary, regularityUnary, gapUnary, observedRegularityGap, cert⟩

theorem CausalCommitmentNameCertObligations [AskSetup] [PackageSetup]
    {observed regularity gap forward transport continuation provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentCarrier observed regularity gap forward transport continuation provenance
        localCert bundle pkg ->
      UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
        UnaryHistory forward ∧ UnaryHistory transport ∧ UnaryHistory continuation ∧
          UnaryHistory provenance ∧ UnaryHistory localCert ∧ Cont observed regularity gap ∧
            Cont gap forward continuation ∧ Cont transport continuation provenance ∧
              PkgSig bundle localCert pkg ∧
                SemanticNameCert
                  (fun row : BHist =>
                    CausalCommitmentCarrier observed regularity gap forward transport
                      continuation provenance localCert bundle pkg ∧ hsame row localCert)
                  (fun row : BHist =>
                    Cont observed regularity gap ∧ Cont gap forward continuation ∧
                      Cont transport continuation provenance ∧ hsame row localCert)
                  (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
                  hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, transportUnary,
    continuationUnary, provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, transportContinuationProvenance, localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CausalCommitmentCarrier observed regularity gap forward transport continuation
            provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          Cont observed regularity gap ∧ Cont gap forward continuation ∧
            Cont transport continuation provenance ∧ hsame row localCert)
        (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localCert (And.intro carrierWitness (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨observedRegularityGap, gapForwardContinuation, transportContinuationProvenance,
          sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨localCertPkg, sourceRow.right⟩
  }
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, transportUnary,
      continuationUnary, provenanceUnary, localCertUnary, observedRegularityGap,
        gapForwardContinuation, transportContinuationProvenance, localCertPkg, cert⟩

theorem CausalCommitmentCarrier_transport [AskSetup] [PackageSetup]
    {observed regularity gap forward transport continuation provenance localCert
      observed' regularity' gap' forward' transport' continuation' provenance'
      localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentCarrier observed regularity gap forward transport continuation provenance
        localCert bundle pkg →
      hsame observed observed' →
      hsame regularity regularity' →
      hsame gap gap' →
      hsame forward forward' →
      hsame transport transport' →
      hsame continuation continuation' →
      hsame provenance provenance' →
      hsame localCert localCert' →
      PkgSig bundle localCert' pkg →
        CausalCommitmentCarrier observed' regularity' gap' forward' transport'
          continuation' provenance' localCert' bundle pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier sameObserved sameRegularity sameGap sameForward sameTransport
    sameContinuation sameProvenance sameLocalCert localCertPkg'
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, transportUnary,
    continuationUnary, provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, transportContinuationProvenance, _localCertPkg⟩ := carrier
  refine
    ⟨unary_transport observedUnary sameObserved,
      unary_transport regularityUnary sameRegularity,
      unary_transport gapUnary sameGap,
      unary_transport forwardUnary sameForward,
      unary_transport transportUnary sameTransport,
      unary_transport continuationUnary sameContinuation,
      unary_transport provenanceUnary sameProvenance,
      unary_transport localCertUnary sameLocalCert,
      cont_hsame_transport sameObserved sameRegularity sameGap observedRegularityGap,
      cont_hsame_transport sameGap sameForward sameContinuation gapForwardContinuation,
      cont_hsame_transport sameTransport sameContinuation sameProvenance
        transportContinuationProvenance,
      localCertPkg'⟩

theorem CausalCommitmentCarrier_forward_binding_route [AskSetup] [PackageSetup]
    {observed regularity gap forward transport continuation provenance localCert routeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentCarrier observed regularity gap forward transport continuation provenance
        localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        PkgSig bundle routeRead pkg ->
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory continuation ∧ UnaryHistory localCert ∧
              UnaryHistory routeRead ∧ Cont observed regularity gap ∧
                Cont gap forward continuation ∧ Cont continuation localCert routeRead ∧
                  PkgSig bundle localCert pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier continuationLocalCertRoute routePkg
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, continuationUnary,
      localCertUnary, routeReadUnary, observedRegularityGap, gapForwardContinuation,
      continuationLocalCertRoute, localCertPkg, routePkg⟩

def CausalCommitmentForwardGapCarrier [AskSetup] [PackageSetup]
    (observed regularity gap forward locality transport continuation provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  CausalCommitmentCarrier observed regularity gap forward transport continuation provenance
      localCert bundle pkg ∧
    UnaryHistory locality ∧ Cont forward locality localCert

theorem CausalCommitmentForwardGapObligations [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      CausalCommitmentCarrier observed regularity gap forward transport continuation
          provenance localCert bundle pkg ∧
        UnaryHistory locality ∧ Cont forward locality localCert ∧
          SemanticNameCert
            (fun row : BHist =>
              CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                transport continuation provenance localCert bundle pkg ∧ hsame row localCert)
            (fun row : BHist =>
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ hsame row localCert)
            (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
            hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CausalCommitmentForwardGapCarrier observed regularity gap forward locality
            transport continuation provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          Cont observed regularity gap ∧ Cont gap forward continuation ∧
            Cont forward locality localCert ∧ hsame row localCert)
        (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localCert (And.intro carrierWitness (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityName,
          sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨localCertPkg, sourceRow.right⟩
  }
  exact And.intro carrier.left (And.intro localityUnary (And.intro forwardLocalityName cert))

theorem CausalCommitmentLocalityCellHandoff [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      Cont continuation localCert routeRead →
        PkgSig bundle routeRead pkg →
          UnaryHistory locality ∧ Cont forward locality localCert ∧ UnaryHistory routeRead ∧
            SemanticNameCert
              (fun row : BHist =>
                CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                  transport continuation provenance localCert bundle pkg ∧ hsame row locality)
              (fun row : BHist =>
                Cont forward locality localCert ∧ Cont continuation localCert routeRead ∧
                  hsame row locality)
              (fun row : BHist =>
                PkgSig bundle localCert pkg ∧ PkgSig bundle routeRead pkg ∧
                  hsame row locality)
              hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationLocalCertRoute routePkg
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, _observedRegularityGap,
    _gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
            continuation provenance localCert bundle pkg ∧ hsame row locality)
        (fun row : BHist =>
          Cont forward locality localCert ∧ Cont continuation localCert routeRead ∧
            hsame row locality)
        (fun row : BHist =>
          PkgSig bundle localCert pkg ∧ PkgSig bundle routeRead pkg ∧
            hsame row locality)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro locality (And.intro carrierWitness (hsame_refl locality))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨forwardLocalityName, continuationLocalCertRoute, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨localCertPkg, routePkg, sourceRow.right⟩
  }
  exact ⟨localityUnary, forwardLocalityName, routeReadUnary, cert⟩

theorem CausalCommitmentLocalityGapReadback [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        PkgSig bundle routeRead pkg ->
          UnaryHistory gap ∧ UnaryHistory locality ∧ Cont observed regularity gap ∧
            Cont gap forward continuation ∧ Cont forward locality localCert ∧
              Cont continuation localCert routeRead ∧ PkgSig bundle localCert pkg ∧
                PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier continuationLocalCertRoute routePkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  exact
    ⟨gapUnary, localityUnary, observedRegularityGap, gapForwardContinuation,
      forwardLocalityName, continuationLocalCertRoute, localCertPkg, routePkg⟩

theorem CausalCommitmentObserverCellNonescape [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg ->
      Cont continuation localCert routeRead ->
        PkgSig bundle routeRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CausalCommitmentForwardGapCarrier observed regularity gap forward locality
                transport continuation provenance localCert bundle pkg ∧ hsame row routeRead)
            (fun row : BHist =>
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ Cont continuation localCert routeRead ∧
                  hsame row routeRead)
            (fun row : BHist =>
              PkgSig bundle localCert pkg ∧ PkgSig bundle routeRead pkg ∧
                hsame row routeRead)
            hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier continuationLocalCertRoute routePkg
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  constructor
  · constructor
    · exact Exists.intro routeRead (And.intro carrierWitness (hsame_refl routeRead))
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
      ⟨observedRegularityGap, gapForwardContinuation, forwardLocalityName,
        continuationLocalCertRoute, sourceRow.right⟩
  · intro _row sourceRow
    exact ⟨localCertPkg, routePkg, sourceRow.right⟩

theorem CausalCommitmentCarrier_classifier_coherence [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
            continuation provenance localCert bundle pkg ∧ hsame row gap)
        (fun row : BHist =>
          hsame row gap ∧ Cont observed regularity gap ∧ Cont gap forward continuation)
        (fun row : BHist =>
          hsame row gap ∧ Cont forward locality localCert ∧ PkgSig bundle localCert pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierWitness := carrier
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨_observedUnary, _regularityUnary, _gapUnary, _forwardUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  constructor
  · constructor
    · exact Exists.intro gap (And.intro carrierWitness (hsame_refl gap))
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
    exact ⟨sourceRow.right, observedRegularityGap, gapForwardContinuation⟩
  · intro _row sourceRow
    exact ⟨sourceRow.right, forwardLocalityName, localCertPkg⟩

theorem CausalCommitmentCarrier_visibility [AskSetup] [PackageSetup]
    {observed regularity gap forward locality transport continuation provenance localCert
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalCommitmentForwardGapCarrier observed regularity gap forward locality transport
        continuation provenance localCert bundle pkg →
      Cont continuation localCert routeRead →
        PkgSig bundle routeRead pkg →
          UnaryHistory observed ∧ UnaryHistory regularity ∧ UnaryHistory gap ∧
            UnaryHistory forward ∧ UnaryHistory locality ∧ UnaryHistory routeRead ∧
              Cont observed regularity gap ∧ Cont gap forward continuation ∧
                Cont forward locality localCert ∧ Cont continuation localCert routeRead ∧
                  PkgSig bundle localCert pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier continuationLocalCertRoute routePkg
  have baseCarrier :
      CausalCommitmentCarrier observed regularity gap forward transport continuation
        provenance localCert bundle pkg :=
    carrier.left
  have localityUnary : UnaryHistory locality :=
    carrier.right.left
  have forwardLocalityName : Cont forward locality localCert :=
    carrier.right.right
  obtain ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, _transportUnary,
    continuationUnary, _provenanceUnary, localCertUnary, observedRegularityGap,
    gapForwardContinuation, _transportContinuationProvenance, localCertPkg⟩ := baseCarrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed continuationUnary localCertUnary continuationLocalCertRoute
  exact
    ⟨observedUnary, regularityUnary, gapUnary, forwardUnary, localityUnary,
      routeReadUnary, observedRegularityGap, gapForwardContinuation, forwardLocalityName,
      continuationLocalCertRoute, localCertPkg, routePkg⟩

end BEDC.Derived.CausalCommitmentUp
