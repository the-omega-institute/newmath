import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

inductive OrderedVectorSpaceUp : Type where
  | mk (V P O A S K H C G N : BHist) : OrderedVectorSpaceUp
  deriving DecidableEq

namespace OrderedVectorSpaceUp

def fields : OrderedVectorSpaceUp → List BHist
  | OrderedVectorSpaceUp.mk V P O A S K H C G N => [V, P, O, A, S, K, H, C, G, N]

theorem fields_faithful :
    ∀ x y : OrderedVectorSpaceUp, fields x = fields y → x = y := by
  intro x y hfields
  cases x with
  | mk V₁ P₁ O₁ A₁ S₁ K₁ H₁ C₁ G₁ N₁ =>
      cases y with
      | mk V₂ P₂ O₂ A₂ S₂ K₂ H₂ C₂ G₂ N₂ =>
          cases hfields
          rfl

theorem carrier_rows_surface :
    fields
        (OrderedVectorSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
      [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  rfl

end OrderedVectorSpaceUp

end BEDC.Derived
