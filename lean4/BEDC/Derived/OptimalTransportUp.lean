import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptimalTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptimalTransportFiniteCouplingPacket [AskSetup] [PackageSetup]
    (source target sourceMass targetMass cost coupling marginal costLedger feasible dual
      provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory marginal ∧ UnaryHistory costLedger ∧ UnaryHistory feasible ∧
        UnaryHistory dual ∧ UnaryHistory provenance ∧ Cont source target marginal ∧
          Cont cost coupling costLedger ∧ Cont marginal costLedger feasible ∧
            Cont feasible dual provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportFiniteCouplingPacket_semantic_name_certificate [AskSetup]
    [PackageSetup]
    {source target sourceMass targetMass cost coupling marginal costLedger feasible dual
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket source target sourceMass targetMass cost coupling
        marginal costLedger feasible dual provenance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          OptimalTransportFiniteCouplingPacket source target sourceMass targetMass cost coupling
              marginal costLedger feasible dual provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          OptimalTransportFiniteCouplingPacket source target sourceMass targetMass cost coupling
              marginal costLedger feasible dual provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          OptimalTransportFiniteCouplingPacket source target sourceMass targetMass cost coupling
              marginal costLedger feasible dual provenance bundle pkg ∧ hsame row provenance)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨packet, hsame_refl provenance⟩
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same carrier
        exact ⟨carrier.left, hsame_trans (hsame_symm same) carrier.right⟩
    }
    pattern_sound := by
      intro _row sourcePacket
      exact sourcePacket
    ledger_sound := by
      intro _row sourcePacket
      exact sourcePacket
  }

end BEDC.Derived.OptimalTransportUp
