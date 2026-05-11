import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.DynSystemUp
import BEDC.Derived.MatrixUp

namespace BEDC.Derived.ControlObservabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.DynSystemUp
open BEDC.Derived.MatrixUp

def ControlObservabilityCarrier [AskSetup] [PackageSetup]
    (state transition output observation stack trace provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory output ∧
    UnaryHistory observation ∧ UnaryHistory stack ∧ UnaryHistory trace ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont transition output observation ∧
        Cont observation stack trace ∧ Cont trace provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlObservabilityCarrier_finite_trace_ledger_readback [AskSetup] [PackageSetup]
    {state transition output observation stack trace provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityCarrier state transition output observation stack trace provenance endpoint
        bundle pkg ->
      UnaryHistory observation ∧ UnaryHistory stack ∧ UnaryHistory trace ∧
        UnaryHistory endpoint ∧ Cont transition output observation ∧ Cont observation stack trace ∧
          Cont trace provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    And.intro carrier.right.right.right.left
      (And.intro carrier.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
                  carrier.right.right.right.right.right.right.right.right.right.right.right))))))

def ControlObservabilityFiniteTraceLedger
    (state transition output observationMatrix traceLedger provenance : BHist) : Prop :=
  Cont state transition observationMatrix ∧ Cont observationMatrix output traceLedger ∧
    hsame provenance BHist.Empty

theorem ControlObservabilityFiniteTraceLedger_readback
    {state transition output observationMatrix traceLedger provenance : BHist} :
    ControlObservabilityFiniteTraceLedger state transition output observationMatrix traceLedger
      provenance ->
      hsame observationMatrix (append state transition) ∧
        hsame traceLedger (append observationMatrix output) ∧ hsame provenance BHist.Empty ∧
          SemanticNameCert (fun row : BHist => row = traceLedger)
            (fun row : BHist => row = traceLedger)
            (fun row : BHist => row = traceLedger) hsame := by
  intro ledger
  cases ledger with
  | intro observationRow ledgerRest =>
      cases ledgerRest with
      | intro traceRow provenanceEmpty =>
          constructor
          · exact observationRow
          · constructor
            · exact traceRow
            · constructor
              · exact provenanceEmpty
              · exact {
                  core := {
                    carrier_inhabited := ⟨traceLedger, rfl⟩
                    equiv_refl := by
                      intro row _source
                      exact hsame_refl row
                    equiv_symm := by
                      intro _row _row' same
                      exact hsame_symm same
                    equiv_trans := by
                      intro _row _row' _row'' sameLeft sameRight
                      exact hsame_trans sameLeft sameRight
                    carrier_respects_equiv := by
                      intro _row _row' same source
                      exact (hsame_symm same).trans source
                  }
                  pattern_sound := by
                    intro _row source
                    exact source
                  ledger_sound := by
                    intro _row source
                    exact source
                }

def ControlObservabilityFiniteObservationPacket [AskSetup] [PackageSetup]
    (state transition output observationRows observationMatrix traceLedger provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory output ∧
    Cont output transition observationRows ∧ Cont observationRows state observationMatrix ∧
      Cont observationMatrix provenance traceLedger ∧
        Cont traceLedger provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlObservabilityFiniteObservationPacket_classifier_transport [AskSetup]
    [PackageSetup]
    {state state' transition transition' output output' observationRows observationRows'
      observationMatrix observationMatrix' traceLedger traceLedger' provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityFiniteObservationPacket state transition output observationRows
        observationMatrix traceLedger provenance endpoint bundle pkg ->
      hsame state state' ->
        hsame transition transition' ->
          hsame output output' ->
            hsame provenance provenance' ->
              Cont output' transition' observationRows' ->
                Cont observationRows' state' observationMatrix' ->
                  Cont observationMatrix' provenance' traceLedger' ->
                    Cont traceLedger' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        ControlObservabilityFiniteObservationPacket state' transition' output'
                            observationRows' observationMatrix' traceLedger' provenance'
                            endpoint' bundle pkg ∧
                          hsame observationRows observationRows' ∧
                            hsame observationMatrix observationMatrix' ∧
                              hsame traceLedger traceLedger' ∧ hsame endpoint endpoint' := by
  intro packet sameState sameTransition sameOutput sameProvenance observationRowsRow
    observationMatrixRow traceLedgerRow endpointRow endpointPkg
  have stateUnary : UnaryHistory state' :=
    unary_transport packet.left sameState
  have transitionUnary : UnaryHistory transition' :=
    unary_transport packet.right.left sameTransition
  have outputUnary : UnaryHistory output' :=
    unary_transport packet.right.right.left sameOutput
  have sameObservationRows : hsame observationRows observationRows' :=
    cont_respects_hsame sameOutput sameTransition packet.right.right.right.left
      observationRowsRow
  have sameObservationMatrix : hsame observationMatrix observationMatrix' :=
    cont_respects_hsame sameObservationRows sameState packet.right.right.right.right.left
      observationMatrixRow
  have sameTraceLedger : hsame traceLedger traceLedger' :=
    cont_respects_hsame sameObservationMatrix sameProvenance
      packet.right.right.right.right.right.left traceLedgerRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTraceLedger sameProvenance
      packet.right.right.right.right.right.right.left endpointRow
  exact And.intro
    (And.intro stateUnary
      (And.intro transitionUnary
        (And.intro outputUnary
          (And.intro observationRowsRow
            (And.intro observationMatrixRow
              (And.intro traceLedgerRow
                (And.intro endpointRow endpointPkg)))))))
    (And.intro sameObservationRows
      (And.intro sameObservationMatrix
        (And.intro sameTraceLedger sameEndpoint)))

theorem ControlObservabilityFiniteObservationPacket_zero_dimensional_observation_ledger
    [AskSetup] [PackageSetup]
    {state transition output traceLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityFiniteObservationPacket state transition output BHist.Empty BHist.Empty
        traceLedger provenance endpoint bundle pkg ->
      hsame output BHist.Empty ∧ hsame transition BHist.Empty ∧ hsame state BHist.Empty ∧
        Cont BHist.Empty provenance traceLedger ∧ Cont traceLedger provenance endpoint ∧
          PkgSig bundle endpoint pkg := by
  intro packet
  have outputTransitionEmpty :
      append output transition = BHist.Empty := packet.right.right.right.left.symm
  have outputEmpty : hsame output BHist.Empty :=
    (append_eq_empty_iff.mp outputTransitionEmpty).left
  have transitionEmpty : hsame transition BHist.Empty :=
    (append_eq_empty_iff.mp outputTransitionEmpty).right
  have stateEmpty : hsame state BHist.Empty :=
    (append_eq_empty_iff.mp packet.right.right.right.right.left.symm).right
  exact
    And.intro outputEmpty
      (And.intro transitionEmpty
        (And.intro stateEmpty
          (And.intro packet.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right))))

def ControlObservabilityCarrierPacket [AskSetup] [PackageSetup]
    (dynSystem matrix vecspace linmap state transition output observationStack traceLedger
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dynSystem ∧ UnaryHistory matrix ∧ UnaryHistory vecspace ∧
    UnaryHistory linmap ∧ UnaryHistory state ∧ Cont transition output observationStack ∧
      Cont observationStack provenance traceLedger ∧ Cont traceLedger provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem ControlObservabilityCarrierPacket_obligation_surface [AskSetup] [PackageSetup]
    {dynSystem matrix vecspace linmap state transition output observationStack traceLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityCarrierPacket dynSystem matrix vecspace linmap state transition output
        observationStack traceLedger provenance endpoint bundle pkg ->
      UnaryHistory dynSystem ∧ UnaryHistory matrix ∧ UnaryHistory vecspace ∧
        UnaryHistory linmap ∧ Cont transition output observationStack ∧
          Cont observationStack provenance traceLedger ∧
            Cont traceLedger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.left
                packet.right.right.right.right.right.right.right.right))))))

def ControlObservationPacket [AskSetup] [PackageSetup]
    (state transition output observationMatrix traceLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory output ∧
    UnaryHistory observationMatrix ∧ UnaryHistory traceLedger ∧ UnaryHistory endpoint ∧
      hsame observationMatrix (append (append state transition) output) ∧
        Cont observationMatrix traceLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlObservationPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {state transition output observationMatrix traceLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservationPacket state transition output observationMatrix traceLedger endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ControlObservationPacket state transition output observationMatrix traceLedger e
                bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ControlObservationPacket state transition output observationMatrix traceLedger e
                bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ControlObservationPacket state transition output observationMatrix traceLedger e
                bundle pkg ∧ hsame row e)
          hsame ∧
        hsame observationMatrix (append (append state transition) output) ∧
          Cont observationMatrix traceLedger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint (Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          cases source with
          | intro e data =>
              exact Exists.intro e
                (And.intro data.left (hsame_trans (hsame_symm same) data.right))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · exact
      And.intro packet.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right)

def ControlObservabilityPacket
    (state transition output observation matrix trace packet : BHist) : Prop :=
  Cont state transition observation ∧ Cont observation output matrix ∧ Cont matrix trace packet

theorem ControlObservabilityPacket_trace_ledger_readback
    {state transition output observation matrix trace packet : BHist}
    (hP : ControlObservabilityPacket state transition output observation matrix trace packet) :
    Cont state (append transition (append output trace)) packet ∧ Cont observation output matrix ∧
      Cont matrix trace packet := by
  have stateTransition : Cont state transition observation :=
    hP.left
  have observationOutput : Cont observation output matrix :=
    hP.right.left
  have matrixTrace : Cont matrix trace packet :=
    hP.right.right
  cases stateTransition
  cases observationOutput
  cases matrixTrace
  constructor
  · exact
      (append_assoc (append state transition) output trace).trans
        (append_assoc state transition (append output trace))
  · constructor
    · rfl
    · rfl
def ControlObservabilityPacket_kernel_separation_carrier
    (state observationMatrix trace provenance : BHist) : Prop :=
  Cont state observationMatrix trace ∧ UnaryHistory provenance

theorem ControlObservabilityPacket_kernel_separation
    {stateA stateB observationMatrix traceA traceB provenanceA provenanceB : BHist}
    (left :
      ControlObservabilityPacket_kernel_separation_carrier stateA observationMatrix traceA
        provenanceA)
    (right :
      ControlObservabilityPacket_kernel_separation_carrier stateB observationMatrix traceB
        provenanceB)
    (sameTrace : hsame traceA traceB) :
    hsame stateA stateB ∧
      Cont stateA observationMatrix traceA ∧
        Cont stateB observationMatrix traceB := by
  have sameState : hsame stateA stateB :=
    cont_right_cancel_hsame_result left.left right.left sameTrace
  exact And.intro sameState (And.intro left.left right.left)

def ControlObservabilityZeroKernelTrace
    (packet stateA stateB diff zero kernel rank trace ledger : BHist) : Prop :=
  Cont stateA diff stateB ∧
    hsame kernel zero ∧
      hsame rank packet ∧ Cont diff kernel zero ∧ Cont stateA trace ledger ∧ Cont stateB trace ledger

theorem ControlObservabilityKernelSeparation_state_rows_hsame
    {packet stateA stateB diff zero kernel rank trace ledger : BHist} :
    ControlObservabilityZeroKernelTrace packet stateA stateB diff zero kernel rank trace ledger ->
      hsame diff zero -> hsame zero BHist.Empty -> Cont stateA trace ledger ->
        Cont stateB trace ledger ->
          hsame stateA stateB /\ Cont stateA trace ledger /\ Cont stateB trace ledger := by
  intro surface sameDiffZero sameZeroEmpty stateATrace stateBTrace
  have diffEmpty : hsame diff BHist.Empty := hsame_trans sameDiffZero sameZeroEmpty
  have stateAStep : Cont stateA BHist.Empty stateB :=
    cont_hsame_transport (hsame_refl stateA) diffEmpty (hsame_refl stateB) surface.left
  have sameStatesFromKernel : hsame stateA stateB :=
    hsame_symm (cont_right_unit_iff.mp stateAStep)
  have sameStatesFromTrace : hsame stateA stateB :=
    cont_right_cancel stateATrace stateBTrace
  exact And.intro
    (hsame_trans (hsame_trans sameStatesFromKernel (hsame_symm sameStatesFromTrace))
      sameStatesFromTrace)
    (And.intro stateATrace stateBTrace)

theorem ControlObservability_finite_trace_ledger_readback [AskSetup] [PackageSetup]
    {phase ode time source target flowWitness endpoint route output observation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DynSystemFlowPacket phase ode time source target flowWitness endpoint route bundle pkg ->
      MatrixSingletonCarrier output -> Cont output endpoint observation ->
        UnaryHistory observation ∧ hsame flowWitness (append (append phase time) source) ∧
          hsame endpoint (append flowWitness ode) ∧ hsame route (append endpoint target) ∧
            MatrixSingletonCarrier output := by
  intro packet outputCarrier observationCont
  have coverage := DynSystemFlowPacket_endpoint_coverage packet
  have outputUnary : UnaryHistory output := by
    cases outputCarrier
    exact unary_empty
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed outputUnary coverage.right.left observationCont
  exact And.intro observationUnary
    (And.intro coverage.right.right.right.left
      (And.intro coverage.right.right.right.right.left
        (And.intro coverage.right.right.right.right.right.left outputCarrier)))

end BEDC.Derived.ControlObservabilityUp
