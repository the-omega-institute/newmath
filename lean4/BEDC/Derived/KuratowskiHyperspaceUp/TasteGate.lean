import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.KuratowskiHyperspaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive KuratowskiHyperspaceUp : Type where
  | mk (H E U F D S C P M : BHist) : KuratowskiHyperspaceUp
  deriving DecidableEq

def kuratowskiHyperspaceFields : KuratowskiHyperspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiHyperspaceUp.mk H E U F D S C P M => [H, E, U, F, D, S, C, P, M]

theorem KuratowskiHyperspaceCarrier_distance_stability
    {H E U F D S C P M route profile completion : BHist} :
    kuratowskiHyperspaceFields (KuratowskiHyperspaceUp.mk H E U F D S C P M) =
        [H, E, U, F, D, S, C, P, M] →
      Cont H F profile →
        Cont E F route →
          Cont U route completion →
            hsame D route →
              hsame S completion →
                hsame D route ∧ hsame S completion ∧ Cont H F profile ∧
                  Cont E F route ∧ Cont U route completion := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _fieldsEq profileRoute embeddingRoute completionRoute distanceStable sealStable
  exact ⟨distanceStable, sealStable, profileRoute, embeddingRoute, completionRoute⟩

end BEDC.Derived.KuratowskiHyperspaceUp
