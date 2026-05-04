import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem CommRingSingletonMul_visible_strictZeroDivisor {h : BHist} :
    CommRingStrictZeroDivisor CommRingSingletonMul (BHist.e0 h) ∧
      CommRingStrictZeroDivisor CommRingSingletonMul (BHist.e1 h) := by
  constructor
  · constructor
    · intro same
      exact not_hsame_e0_empty same
    · exact
        Exists.intro (BHist.e1 h)
          (And.intro
            (fun same => not_hsame_e1_empty same)
            (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
  · constructor
    · intro same
      exact not_hsame_e1_empty same
    · exact
        Exists.intro (BHist.e0 h)
          (And.intro
            (fun same => not_hsame_e0_empty same)
            (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))

end BEDC.Derived.CommRingUp
