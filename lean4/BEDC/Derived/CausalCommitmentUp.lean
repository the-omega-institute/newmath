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
  exact
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

end BEDC.Derived.CausalCommitmentUp
