import BEDC.Derived.SheafUp.RefinementGluing

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafBHistPointGermLedger_refinement_tower_gluing
    {point openA openB openC sectionA germA refinedGerm intermediateGlobal finalGlobal :
      BHist} :
    SheafBHistPointGermLedger point openA sectionA germA -> hsame openA openB ->
      Cont openB sectionA refinedGerm -> hsame openB openC ->
        Cont openC sectionA intermediateGlobal -> Cont openA sectionA finalGlobal ->
          Cont openC sectionA finalGlobal -> hsame germA finalGlobal ->
            SheafBHistPointGermLedger point openC sectionA intermediateGlobal ∧
              hsame intermediateGlobal finalGlobal := by
  intro ledger sameAB refinedRow sameBC intermediateRow finalRow finalRefinedRow sameFinal
  have first :
      SheafBHistPointGermLedger point openB sectionA refinedGerm ∧
        hsame refinedGerm refinedGerm ∧ hsame finalGlobal refinedGerm :=
    SheafRefinementGluing_descent_cont
      ledger sameAB refinedRow finalRow refinedRow sameFinal
  have sameRefinedFinal : hsame refinedGerm finalGlobal :=
    hsame_symm first.right.right
  have finalOnB : Cont openB sectionA finalGlobal :=
    cont_result_hsame_transport refinedRow sameRefinedFinal
  have second :
      SheafBHistPointGermLedger point openC sectionA intermediateGlobal ∧
        hsame intermediateGlobal finalGlobal ∧ hsame finalGlobal finalGlobal :=
    SheafRefinementGluing_descent_cont
      first.left sameBC intermediateRow finalOnB finalRefinedRow sameRefinedFinal
  exact And.intro second.left second.right.left

end BEDC.Derived.SheafUp
