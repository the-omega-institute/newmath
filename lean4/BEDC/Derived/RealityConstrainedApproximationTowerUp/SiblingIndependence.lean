import BEDC.Derived.RealityConstrainedApproximationTowerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedApproximationTowerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedApproximationTower_sibling_independence_boundary
    (x : RealityConstrainedApproximationTowerUp) :
    Exists fun O : BHist =>
      Exists fun D : BHist =>
        Exists fun M : BHist =>
          Exists fun S : BHist =>
            Exists fun C : BHist =>
              Exists fun F : BHist =>
                Exists fun L : BHist =>
                  Exists fun H : BHist =>
                    Exists fun R : BHist =>
                      Exists fun P : BHist =>
                        Exists fun N : BHist =>
                          Exists fun modelRead : BHist =>
                            Exists fun signatureRead : BHist =>
                              Exists fun ledgerRead : BHist =>
                                Exists fun publicRead : BHist =>
                                  x = RealityConstrainedApproximationTowerUp.mk O D M S C F L H R
                                      P N ∧
                                    realityConstrainedApproximationTowerFields x =
                                      [O, D, M, S, C, F, L, H, R, P, N] ∧
                                      Cont O D modelRead ∧
                                        Cont modelRead S signatureRead ∧
                                          Cont signatureRead F ledgerRead ∧
                                            Cont ledgerRead L publicRead ∧
                                              hsame publicRead
                                                (append (append (append O D) S) (append F L)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk O D M S C F L H R P N =>
      refine ⟨O, D, M, S, C, F, L, H, R, P, N, append O D, append (append O D) S,
        append (append (append O D) S) F,
        append (append (append O D) S) (append F L), ?_⟩
      exact
        ⟨rfl, rfl, rfl, rfl, rfl,
          (append_assoc (append (append O D) S) F L).symm, rfl⟩

end BEDC.Derived.RealityConstrainedApproximationTowerUp
