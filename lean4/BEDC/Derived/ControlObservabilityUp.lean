import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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

end BEDC.Derived.ControlObservabilityUp
