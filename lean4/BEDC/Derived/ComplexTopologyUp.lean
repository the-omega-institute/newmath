import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.HolomorphicUp

theorem ComplexTopologyOpenDisk_point_radius_suffix_closed {z0 r z extra r' z' : BHist} :
    OpenDisk z0 r z -> UnaryHistory extra -> Cont r extra r' -> Cont z extra z' ->
      OpenDisk z0 r' z' ∧ ∃ gap : BHist,
        UnaryHistory gap ∧ Cont gap z r ∧ Cont gap z' r' := by
  intro disk extraUnary radiusExtra pointExtra
  cases disk with
  | intro centerCarrier diskRest =>
      cases diskRest with
      | intro radiusUnary diskRest =>
          cases diskRest with
          | intro pointCarrier gapWitness =>
              cases gapWitness with
              | intro gap gapData =>
                  cases gapData with
                  | intro gapUnary gapPoint =>
                      have radiusUnary' : UnaryHistory r' :=
                        unary_cont_closed radiusUnary extraUnary radiusExtra
                      have shiftedPointCarrier : ComplexHistoryCarrier z' :=
                        BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport pointExtra.symm
                          (ComplexHistoryCarrier_append_unary_closed pointCarrier extraUnary)
                      have shiftedGapPoint : Cont gap z' r' := by
                        cases gapPoint
                        cases pointExtra
                        cases radiusExtra
                        exact append_assoc gap z extra
                      exact And.intro
                        (And.intro centerCarrier
                          (And.intro radiusUnary'
                            (And.intro shiftedPointCarrier
                              (Exists.intro gap (And.intro gapUnary shiftedGapPoint)))))
                        (Exists.intro gap
                          (And.intro gapUnary (And.intro gapPoint shiftedGapPoint)))

end BEDC.Derived.ComplexTopologyUp
