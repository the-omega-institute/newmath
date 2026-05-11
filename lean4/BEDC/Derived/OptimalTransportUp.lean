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

def OptimalTransportPacket [AskSetup] [PackageSetup]
    (source target massSource massTarget cost coupling marginal objective feasible dual provenance :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory massSource ∧
    UnaryHistory massTarget ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory marginal ∧ UnaryHistory objective ∧ UnaryHistory feasible ∧
        UnaryHistory dual ∧ UnaryHistory provenance ∧ Cont source target coupling ∧
          Cont cost coupling objective ∧ Cont marginal objective feasible ∧
            Cont feasible dual provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {source target massSource massTarget cost coupling marginal objective feasible dual provenance :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportPacket source target massSource massTarget cost coupling marginal
        objective feasible dual provenance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          OptimalTransportPacket source target massSource massTarget cost coupling marginal
            objective feasible dual provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          OptimalTransportPacket source target massSource massTarget cost coupling marginal
            objective feasible dual provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          OptimalTransportPacket source target massSource massTarget cost coupling marginal
            objective feasible dual provenance bundle pkg ∧ hsame row provenance)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig NameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro packet (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.OptimalTransportUp
