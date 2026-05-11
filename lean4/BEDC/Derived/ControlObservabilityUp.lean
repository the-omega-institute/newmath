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

end BEDC.Derived.ControlObservabilityUp
