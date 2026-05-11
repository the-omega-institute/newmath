import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlObservabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

def ControlObservabilityCarrier [AskSetup] [PackageSetup]
    (state transition output observation trace ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧
    UnaryHistory transition ∧
      UnaryHistory output ∧
        UnaryHistory ledger ∧
          Cont transition output observation ∧
            Cont state observation trace ∧
              Cont trace ledger endpoint ∧
                PkgSig bundle endpoint pkg

theorem ControlObservabilityCarrier_ledger_readback [AskSetup] [PackageSetup]
    {state transition output observation trace ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityCarrier state transition output observation trace ledger endpoint
      bundle pkg ->
        UnaryHistory observation ∧
          UnaryHistory trace ∧
            UnaryHistory endpoint ∧
              hsame observation (append transition output) ∧
                hsame trace (append state observation) ∧
                  hsame endpoint (append trace ledger) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.right.left
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed carrier.left observationUnary
      carrier.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  exact And.intro observationUnary
    (And.intro traceUnary
      (And.intro endpointUnary
        (And.intro carrier.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.left
              carrier.right.right.right.right.right.right.right)))))

end BEDC.Derived.ControlObservabilityUp
