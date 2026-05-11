import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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
