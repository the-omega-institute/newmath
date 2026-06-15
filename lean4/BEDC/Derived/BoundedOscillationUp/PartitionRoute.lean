import BEDC.Derived.BoundedOscillationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BoundedOscillationUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BoundedVariationOscillationPartitionRoute [AskSetup] [PackageSetup]
    {I W R D L B S H C P N windowRead ledgerRead partitionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I W windowRead ->
      Cont D L ledgerRead ->
        Cont ledgerRead S partitionRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row partitionRead)
                (fun row : BHist =>
                  hsame row I ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                    hsame row L ∨ hsame row B ∨ hsame row S ∨ hsame row H ∨
                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row partitionRead)
                (fun row : BHist =>
                  Cont I W windowRead ∧ Cont D L ledgerRead ∧
                    Cont ledgerRead S partitionRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg ∧ hsame row partitionRead)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro windowRoute ledgerRoute partitionRoute provenancePkg localNamePkg
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · exact ⟨partitionRead, hsame_refl partitionRead⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows source
    exact hsame_trans (hsame_symm sameRows) source
  · intro _row source
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr source))))))))))
  · intro _row source
    exact
      ⟨windowRoute, ledgerRoute, partitionRoute, provenancePkg, localNamePkg, source⟩

end BEDC.Derived.BoundedOscillationUp.TasteGate
