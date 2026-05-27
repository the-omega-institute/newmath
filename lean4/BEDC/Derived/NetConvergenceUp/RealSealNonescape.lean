import BEDC.Derived.NetConvergenceUp

namespace BEDC.Derived.NetConvergenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem NetConvergenceCarrier_real_seal_nonescape
    {D T E A F S R L H C P M filterRead streamRead sealRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D T E →
        Cont E F filterRead →
          Cont F S streamRead →
            Cont streamRead R sealRead →
              hsame sealRead L →
                Cont D T E ∧ Cont E F filterRead ∧ Cont F S streamRead ∧
                  Cont streamRead R sealRead ∧ hsame sealRead L ∧ hsame L L ∧
                    netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
                      [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier directedRoute filterRoute streamRoute sealRoute sealSame
  obtain ⟨_sameD, _sameT, _sameE, _sameA, _sameF, _sameS, _sameR, sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact
    ⟨directedRoute, filterRoute, streamRoute, sealRoute, sealSame, sameL, fields⟩

end BEDC.Derived.NetConvergenceUp
