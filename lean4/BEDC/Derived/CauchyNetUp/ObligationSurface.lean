import BEDC.Derived.CauchyNetUp.TasteGate

namespace BEDC.Derived.CauchyNetUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CauchyNetNameCert_obligation_surface {D S R W T L H C P N : BHist} :
    cauchyNetFields (CauchyNetUp.mk D S R W T L H C P N) =
        [D, S, R, W, T, L, H, C, P, N] /\
      cauchyNetToEventFlow (CauchyNetUp.mk D S R W T L H C P N) =
        [cauchyNetEncodeBHist D,
          cauchyNetEncodeBHist S,
          cauchyNetEncodeBHist R,
          cauchyNetEncodeBHist W,
          cauchyNetEncodeBHist T,
          cauchyNetEncodeBHist L,
          cauchyNetEncodeBHist H,
          cauchyNetEncodeBHist C,
          cauchyNetEncodeBHist P,
          cauchyNetEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate NameCert
  exact ⟨rfl, rfl⟩

end BEDC.Derived.CauchyNetUp
