import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionClassifierSpec_hsame_e1_map_iff {x y : OptionCarrier BHist} :
    OptionClassifierSpec hsame (Option.map BHist.e1 x) (Option.map BHist.e1 y) ↔
      OptionClassifierSpec hsame x y := by
  constructor
  · intro sameMapped
    cases x with
    | none =>
        cases y with
        | none =>
            exact sameMapped
        | some _ =>
            cases sameMapped
    | some _ =>
        cases y with
        | none =>
            cases sameMapped
        | some _ =>
            exact hsame_e1_iff.mp sameMapped
  · intro sameSource
    cases x with
    | none =>
        cases y with
        | none =>
            exact sameSource
        | some _ =>
            cases sameSource
    | some _ =>
        cases y with
        | none =>
            cases sameSource
        | some _ =>
            exact hsame_e1_iff.mpr sameSource

end BEDC.Derived.OptionUp
