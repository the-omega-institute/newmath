import BEDC.Derived.LargeModelCorpusSupplyUp.TasteGate

namespace BEDC.Derived.LargeModelCorpusSupplyUp

open BEDC.FKernel.Hist

def LargeModelCorpusSupplyClassifier
    (R F W I A K P N R' F' W' I' A' K' P' N' : BHist) : Prop :=
  hsame R R' ∧ hsame F F' ∧ hsame W W' ∧ hsame I I' ∧ hsame A A' ∧
    hsame K K' ∧ hsame P P' ∧ hsame N N'

theorem LargeModelCorpusSupplyClassifier_refl {R F W I A K P N : BHist} :
    LargeModelCorpusSupplyClassifier R F W I A K P N R F W I A K P N := by
  -- BEDC touchpoint anchor: BHist hsame
  exact
    ⟨hsame_refl R, hsame_refl F, hsame_refl W, hsame_refl I, hsame_refl A,
      hsame_refl K, hsame_refl P, hsame_refl N⟩

end BEDC.Derived.LargeModelCorpusSupplyUp
