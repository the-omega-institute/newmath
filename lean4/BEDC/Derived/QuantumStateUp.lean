import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.QuantumStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def QuantumStateBHistCarrier [AskSetup] [PackageSetup]
    (hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory projective ∧ UnaryHistory vector ∧ UnaryHistory norm ∧
    UnaryHistory phase ∧ UnaryHistory projectiveEndpoint ∧ UnaryHistory provenance ∧
      Cont hilbert vector hilbertLedger ∧ Cont projective projectiveEndpoint projectiveLedger ∧
        Cont vector norm phase ∧ Cont provenance (append hilbertLedger projectiveLedger) endpoint ∧
          PkgSig bundle endpoint pkg

theorem QuantumStateBHistCarrier_hilbert_source_boundary [AskSetup] [PackageSetup]
    {hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuantumStateBHistCarrier hilbert projective vector norm phase projectiveEndpoint
        hilbertLedger projectiveLedger provenance endpoint bundle pkg ->
      UnaryHistory vector ∧ UnaryHistory norm ∧ UnaryHistory hilbertLedger ∧
        Cont hilbert vector hilbertLedger ∧ Cont vector norm phase ∧
          hsame endpoint (append provenance (append hilbertLedger projectiveLedger)) ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  have vectorUnary : UnaryHistory vector :=
    carrier.right.right.left
  have normUnary : UnaryHistory norm :=
    carrier.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.left
  have hilbertLedgerRow : Cont hilbert vector hilbertLedger :=
    carrier.right.right.right.right.right.right.right.left
  have projectiveLedgerRow : Cont projective projectiveEndpoint projectiveLedger :=
    carrier.right.right.right.right.right.right.right.right.left
  have phaseRow : Cont vector norm phase :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance (append hilbertLedger projectiveLedger) endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have hilbertLedgerUnary : UnaryHistory hilbertLedger :=
    unary_cont_closed carrier.left vectorUnary hilbertLedgerRow
  have projectiveLedgerUnary : UnaryHistory projectiveLedger :=
    unary_cont_closed carrier.right.left carrier.right.right.right.right.right.left
      projectiveLedgerRow
  have combinedLedgerUnary : UnaryHistory (append hilbertLedger projectiveLedger) :=
    unary_append_closed hilbertLedgerUnary projectiveLedgerUnary
  have _endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary combinedLedgerUnary endpointRow
  exact And.intro vectorUnary
    (And.intro normUnary
      (And.intro hilbertLedgerUnary
        (And.intro hilbertLedgerRow
          (And.intro phaseRow
            (And.intro endpointRow pkgSig)))))

theorem QuantumStateBHistCarrier_provenance_row_exactness [AskSetup] [PackageSetup]
    {hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuantumStateBHistCarrier hilbert projective vector norm phase projectiveEndpoint
        hilbertLedger projectiveLedger provenance endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory hilbertLedger ∧ UnaryHistory projectiveLedger ∧
        UnaryHistory endpoint ∧ Cont hilbert vector hilbertLedger ∧
          Cont projective projectiveEndpoint projectiveLedger ∧
            Cont provenance (append hilbertLedger projectiveLedger) endpoint ∧
              hsame endpoint (append provenance (append hilbertLedger projectiveLedger)) ∧
                PkgSig bundle endpoint pkg := by
  intro carrier
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.left
  have hilbertLedgerRow : Cont hilbert vector hilbertLedger :=
    carrier.right.right.right.right.right.right.right.left
  have projectiveLedgerRow : Cont projective projectiveEndpoint projectiveLedger :=
    carrier.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance (append hilbertLedger projectiveLedger) endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have hilbertLedgerUnary : UnaryHistory hilbertLedger :=
    unary_cont_closed carrier.left carrier.right.right.left hilbertLedgerRow
  have projectiveLedgerUnary : UnaryHistory projectiveLedger :=
    unary_cont_closed carrier.right.left carrier.right.right.right.right.right.left
      projectiveLedgerRow
  have combinedLedgerUnary : UnaryHistory (append hilbertLedger projectiveLedger) :=
    unary_append_closed hilbertLedgerUnary projectiveLedgerUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary combinedLedgerUnary endpointRow
  exact And.intro provenanceUnary
    (And.intro hilbertLedgerUnary
      (And.intro projectiveLedgerUnary
        (And.intro endpointUnary
          (And.intro hilbertLedgerRow
            (And.intro projectiveLedgerRow
              (And.intro endpointRow
                (And.intro endpointRow
                  carrier.right.right.right.right.right.right.right.right.right.right.right)))))))

theorem QuantumStateBHistCarrier_global_phase_stability [AskSetup] [PackageSetup]
    {hilbert projective vector vector' norm norm' phase phase' projectiveEndpoint
      projectiveEndpoint' hilbertLedger hilbertLedger' projectiveLedger projectiveLedger'
      provenance endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuantumStateBHistCarrier hilbert projective vector norm phase projectiveEndpoint
        hilbertLedger projectiveLedger provenance endpoint bundle pkg ->
      hsame vector vector' ->
        hsame norm norm' ->
          hsame projectiveEndpoint projectiveEndpoint' ->
            Cont hilbert vector' hilbertLedger' ->
              Cont projective projectiveEndpoint' projectiveLedger' ->
                Cont vector' norm' phase' ->
                  Cont provenance (append hilbertLedger' projectiveLedger') endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      QuantumStateBHistCarrier hilbert projective vector' norm' phase'
                          projectiveEndpoint' hilbertLedger' projectiveLedger' provenance
                          endpoint' bundle pkg ∧
                        hsame phase phase' ∧ hsame hilbertLedger hilbertLedger' ∧
                          hsame projectiveLedger projectiveLedger' ∧
                            hsame endpoint endpoint' := by
  intro carrier sameVector sameNorm sameProjectiveEndpoint hilbertLedgerRow'
    projectiveLedgerRow' phaseRow' endpointRow' pkgSig'
  have vectorUnary' : UnaryHistory vector' :=
    unary_transport carrier.right.right.left sameVector
  have normUnary' : UnaryHistory norm' :=
    unary_transport carrier.right.right.right.left sameNorm
  have phaseUnary' : UnaryHistory phase' :=
    unary_cont_closed vectorUnary' normUnary' phaseRow'
  have projectiveEndpointUnary' : UnaryHistory projectiveEndpoint' :=
    unary_transport carrier.right.right.right.right.right.left sameProjectiveEndpoint
  have hilbertLedgerUnary' : UnaryHistory hilbertLedger' :=
    unary_cont_closed carrier.left vectorUnary' hilbertLedgerRow'
  have projectiveLedgerUnary' : UnaryHistory projectiveLedger' :=
    unary_cont_closed carrier.right.left projectiveEndpointUnary' projectiveLedgerRow'
  have samePhase : hsame phase phase' :=
    cont_respects_hsame sameVector sameNorm
      carrier.right.right.right.right.right.right.right.right.right.left phaseRow'
  have sameHilbertLedger : hsame hilbertLedger hilbertLedger' :=
    cont_respects_hsame (hsame_refl hilbert) sameVector
      carrier.right.right.right.right.right.right.right.left hilbertLedgerRow'
  have sameProjectiveLedger : hsame projectiveLedger projectiveLedger' :=
    cont_respects_hsame (hsame_refl projective) sameProjectiveEndpoint
      carrier.right.right.right.right.right.right.right.right.left projectiveLedgerRow'
  have sameCombinedLedger :
      hsame (append hilbertLedger projectiveLedger) (append hilbertLedger' projectiveLedger') :=
    congrArg (fun row : BHist => append row projectiveLedger) sameHilbertLedger |>.trans
      (congrArg (fun row : BHist => append hilbertLedger' row) sameProjectiveLedger)
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameCombinedLedger
      carrier.right.right.right.right.right.right.right.right.right.right.left endpointRow'
  have carrier' :
      QuantumStateBHistCarrier hilbert projective vector' norm' phase' projectiveEndpoint'
        hilbertLedger' projectiveLedger' provenance endpoint' bundle pkg :=
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro vectorUnary'
          (And.intro normUnary'
            (And.intro phaseUnary'
              (And.intro projectiveEndpointUnary'
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro hilbertLedgerRow'
                    (And.intro projectiveLedgerRow'
                      (And.intro phaseRow'
                        (And.intro endpointRow' pkgSig'))))))))))
  exact And.intro carrier'
    (And.intro samePhase
      (And.intro sameHilbertLedger
        (And.intro sameProjectiveLedger sameEndpoint)))

theorem QuantumStateBHistCarrier_projective_phase_classifier [AskSetup] [PackageSetup]
    {hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuantumStateBHistCarrier hilbert projective vector norm phase projectiveEndpoint
        hilbertLedger projectiveLedger provenance endpoint bundle pkg ->
      UnaryHistory phase ∧ hsame phase (append vector norm) ∧
        UnaryHistory projectiveLedger ∧
          hsame projectiveLedger (append projective projectiveEndpoint) ∧
            hsame endpoint (append provenance (append hilbertLedger projectiveLedger)) ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  have phaseRow : Cont vector norm phase :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have projectiveLedgerRow : Cont projective projectiveEndpoint projectiveLedger :=
    carrier.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance (append hilbertLedger projectiveLedger) endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have projectiveLedgerUnary : UnaryHistory projectiveLedger :=
    unary_cont_closed carrier.right.left carrier.right.right.right.right.right.left
      projectiveLedgerRow
  exact And.intro carrier.right.right.right.right.left
    (And.intro phaseRow
      (And.intro projectiveLedgerUnary
        (And.intro projectiveLedgerRow
          (And.intro endpointRow
            carrier.right.right.right.right.right.right.right.right.right.right.right))))

theorem QuantumStateBHistCarrier_observable_expectation_input_exactness [AskSetup] [PackageSetup]
    {hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuantumStateBHistCarrier hilbert projective vector norm phase projectiveEndpoint
        hilbertLedger projectiveLedger provenance endpoint bundle pkg ->
      UnaryHistory hilbert ∧ UnaryHistory vector ∧ UnaryHistory norm ∧ UnaryHistory phase ∧
        UnaryHistory projectiveEndpoint ∧ UnaryHistory hilbertLedger ∧
          UnaryHistory projectiveLedger ∧ hsame phase (append vector norm) ∧
            hsame projectiveLedger (append projective projectiveEndpoint) ∧
              hsame endpoint (append provenance (append hilbertLedger projectiveLedger)) ∧
                PkgSig bundle endpoint pkg := by
  intro carrier
  have hilbertBoundary :=
    QuantumStateBHistCarrier_hilbert_source_boundary carrier
  have projectiveClassifier :=
    QuantumStateBHistCarrier_projective_phase_classifier carrier
  exact And.intro carrier.left
    (And.intro hilbertBoundary.left
      (And.intro hilbertBoundary.right.left
        (And.intro projectiveClassifier.left
          (And.intro carrier.right.right.right.right.right.left
            (And.intro hilbertBoundary.right.right.left
              (And.intro projectiveClassifier.right.right.left
                (And.intro projectiveClassifier.right.left
                  (And.intro projectiveClassifier.right.right.right.left
                    (And.intro projectiveClassifier.right.right.right.right.left
                      projectiveClassifier.right.right.right.right.right)))))))))

def QuantumStatePhaseLedgerSpine (start : BHist) : List BHist -> BHist -> Prop
  | [], final => hsame final start
  | row :: rows, final =>
      UnaryHistory row ∧
        exists next : BHist, Cont start row next ∧ QuantumStatePhaseLedgerSpine next rows final

private theorem QuantumStatePhaseLedgerSpine_normalized_cont_aux
    {start final : BHist} {rows : List BHist} :
    QuantumStatePhaseLedgerSpine start rows final ->
      exists ledger : BHist, UnaryHistory ledger ∧ Cont start ledger final := by
  intro spine
  induction rows generalizing start final with
  | nil =>
      exact Exists.intro BHist.Empty (And.intro unary_empty spine)
  | cons row rows ih =>
      cases spine with
      | intro rowUnary nextData =>
          cases nextData with
          | intro next nextRows =>
              cases nextRows with
              | intro rowCont tailSpine =>
                  have tailPack := ih tailSpine
                  cases tailPack with
                  | intro tail tailRows =>
                      have ledgerUnary : UnaryHistory (append row tail) :=
                        unary_append_closed rowUnary tailRows.left
                      have ledgerCont : Cont start (append row tail) final :=
                        hsame_trans tailRows.right
                          ((congrArg (fun h : BHist => append h tail) rowCont).trans
                            (append_assoc start row tail))
                      exact Exists.intro (append row tail) (And.intro ledgerUnary ledgerCont)

theorem QuantumStatePhaseLedgerSpine_normalized_cont [AskSetup] [PackageSetup]
    {vector norm phase final : BHist} {rows : List BHist} :
    QuantumStatePhaseLedgerSpine phase rows final -> hsame phase (append vector norm) ->
      exists ledger : BHist, UnaryHistory ledger ∧ Cont (append vector norm) ledger final := by
  intro spine phaseNorm
  have ledgerPack := QuantumStatePhaseLedgerSpine_normalized_cont_aux spine
  cases ledgerPack with
  | intro ledger ledgerRows =>
      have ledgerCont : Cont (append vector norm) ledger final :=
        hsame_trans ledgerRows.right (congrArg (fun h : BHist => append h ledger) phaseNorm)
      exact Exists.intro ledger (And.intro ledgerRows.left ledgerCont)

end BEDC.Derived.QuantumStateUp
