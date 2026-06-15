import BEDC.Derived.CauchyWitnessGluingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessGluingCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {ledger tail synchronizer classifier stream regular dyadic realSeal witnessEdge transports
      continuations provenance nameCert realRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont stream dyadic regular ->
      Cont regular realSeal realRead ->
        Cont tail realRead consumer ->
          PkgSig bundle consumer pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row consumer ∧
                  ∃ packet : CauchyWitnessGluingUp,
                    packet = CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream
                      regular dyadic realSeal witnessEdge transports continuations provenance
                      nameCert)
              (fun row : BHist =>
                Cont stream dyadic regular ∧ Cont regular realSeal realRead ∧
                  Cont tail realRead consumer ∧ hsame row consumer)
              (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro streamRegular regularSeal tailConsumer consumerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer
          ⟨hsame_refl consumer,
            Exists.intro
              (CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream regular dyadic
                realSeal witnessEdge transports continuations provenance nameCert)
              rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨streamRegular, regularSeal, tailConsumer, sourceRow.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, consumerPkg⟩
  }

end BEDC.Derived.CauchyWitnessGluingUp
