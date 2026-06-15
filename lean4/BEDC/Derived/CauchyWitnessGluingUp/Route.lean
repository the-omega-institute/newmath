import BEDC.Derived.CauchyWitnessGluingUp.TasteGate

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessGluingCarrier_tail_envelope_handoff [AskSetup] [PackageSetup]
    {ledger tail synchronizer classifier stream regular dyadic realSeal witnessEdge transports
      continuations provenance nameCert tailRead regularRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont tail stream tailRead ->
      Cont stream dyadic regularRead ->
        Cont regularRead realSeal consumer ->
          PkgSig bundle consumer pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row consumer ∧
                  ∃ packet : CauchyWitnessGluingUp,
                    packet = CauchyWitnessGluingUp.mk ledger tail synchronizer classifier stream
                      regular dyadic realSeal witnessEdge transports continuations provenance
                      nameCert)
              (fun row : BHist =>
                Cont tail stream tailRead ∧ Cont stream dyadic regularRead ∧
                  Cont regularRead realSeal consumer ∧ hsame row consumer)
              (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro tailStream streamDyadic regularReal consumerPkg
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
      exact ⟨tailStream, streamDyadic, regularReal, sourceRow.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, consumerPkg⟩
  }

end BEDC.Derived.CauchyWitnessGluingUp
