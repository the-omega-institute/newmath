import BEDC.Derived.RegularCauchyHausdorffReflectionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RegularCauchyHausdorffReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RegularCauchyHausdorffReflectionRepresentativeIndependence
    {x : RegularCauchyHausdorffReflectionUp}
    {leftRight dyadicRead uniquenessRead realRead : BHist} :
    Cont x.leftWindow x.rightWindow leftRight →
      Cont leftRight x.toleranceLedger dyadicRead →
        Cont dyadicRead x.uniquenessRow uniquenessRead →
          Cont uniquenessRead x.realSeal realRead →
            regularCauchyHausdorffReflectionFromEventFlow
                (regularCauchyHausdorffReflectionToEventFlow x) =
              some x ∧
              Cont dyadicRead x.uniquenessRow uniquenessRead ∧
                Cont uniquenessRead x.realSeal realRead := by
  -- BEDC touchpoint anchor: BHist Cont
  intro _leftRightRoute _dyadicRoute uniquenessRoute realSealRoute
  constructor
  · cases x with
    | mk X Y S T D U E H C P N =>
        change
          some
            (RegularCauchyHausdorffReflectionUp.mk
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist X))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist Y))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist S))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist T))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist D))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist U))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist E))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist H))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist C))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist P))
              (regularCauchyHausdorffReflectionDecodeBHist
                (regularCauchyHausdorffReflectionEncodeBHist N))) =
            some (RegularCauchyHausdorffReflectionUp.mk X Y S T D U E H C P N)
        have hdecode :=
          (RegularCauchyHausdorffReflectionTasteGate_single_carrier_alignment).left
        rw [hdecode X, hdecode Y, hdecode S, hdecode T, hdecode D, hdecode U,
          hdecode E, hdecode H, hdecode C, hdecode P, hdecode N]
  · exact ⟨uniquenessRoute, realSealRoute⟩

end BEDC.Derived.RegularCauchyHausdorffReflectionUp
