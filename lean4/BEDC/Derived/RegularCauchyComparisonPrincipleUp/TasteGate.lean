import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyComparisonPrincipleUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyComparisonPrincipleUp : Type where
  | mk (X Y W D E T Q R H C K N : BHist) : RegularCauchyComparisonPrincipleUp
  deriving DecidableEq

def regularCauchyComparisonPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyComparisonPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyComparisonPrincipleEncodeBHist h

def regularCauchyComparisonPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyComparisonPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyComparisonPrincipleDecodeBHist tail)

private theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyComparisonPrincipleFields :
    RegularCauchyComparisonPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyComparisonPrincipleUp.mk X Y W D E T Q R H C K N =>
      [X, Y, W, D, E, T, Q, R, H, C, K, N]

def regularCauchyComparisonPrincipleToEventFlow :
    RegularCauchyComparisonPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyComparisonPrincipleFields x).map
        regularCauchyComparisonPrincipleEncodeBHist

private def regularCauchyComparisonPrincipleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyComparisonPrincipleEventAtDefault index rest

def regularCauchyComparisonPrincipleFromEventFlow
    (ef : EventFlow) : Option RegularCauchyComparisonPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyComparisonPrincipleUp.mk
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 0 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 1 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 2 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 3 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 4 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 5 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 6 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 7 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 8 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 9 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 10 ef))
      (regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEventAtDefault 11 ef)))

private theorem regularCauchyComparisonPrinciple_mk_congr
    {X X' Y Y' W W' D D' E E' T T' Q Q' R R' H H' C C' K K' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hW : W' = W) (hD : D' = D)
    (hE : E' = E) (hT : T' = T) (hQ : Q' = Q) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hK : K' = K) (hN : N' = N) :
    RegularCauchyComparisonPrincipleUp.mk X' Y' W' D' E' T' Q' R' H' C' K' N' =
      RegularCauchyComparisonPrincipleUp.mk X Y W D E T Q R H C K N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hW
  cases hD
  cases hE
  cases hT
  cases hQ
  cases hR
  cases hH
  cases hC
  cases hK
  cases hN
  rfl

private theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyComparisonPrincipleUp,
      regularCauchyComparisonPrincipleFromEventFlow
        (regularCauchyComparisonPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D E T Q R H C K N =>
      exact
        congrArg some
          (regularCauchyComparisonPrinciple_mk_congr
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode X)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode Y)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode W)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode D)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode E)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode T)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode Q)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode R)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode H)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode C)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode K)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode N))

private theorem regularCauchyComparisonPrincipleToEventFlow_injective
    {x y : RegularCauchyComparisonPrincipleUp} :
    regularCauchyComparisonPrincipleToEventFlow x =
      regularCauchyComparisonPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyComparisonPrincipleFromEventFlow
          (regularCauchyComparisonPrincipleToEventFlow x) =
        regularCauchyComparisonPrincipleFromEventFlow
          (regularCauchyComparisonPrincipleToEventFlow y) :=
    congrArg regularCauchyComparisonPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyComparisonPrincipleBHistCarrier :
    BHistCarrier RegularCauchyComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyComparisonPrincipleToEventFlow
  fromEventFlow := regularCauchyComparisonPrincipleFromEventFlow

instance regularCauchyComparisonPrincipleChapterTasteGate :
    ChapterTasteGate RegularCauchyComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyComparisonPrincipleFromEventFlow
        (regularCauchyComparisonPrincipleToEventFlow x) = some x
    exact RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyComparisonPrincipleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyComparisonPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyComparisonPrincipleChapterTasteGate

theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyComparisonPrincipleUp,
        regularCauchyComparisonPrincipleFromEventFlow
          (regularCauchyComparisonPrincipleToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyComparisonPrincipleUp,
          regularCauchyComparisonPrincipleToEventFlow x =
            regularCauchyComparisonPrincipleToEventFlow y → x = y) ∧
          regularCauchyComparisonPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode,
      RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => regularCauchyComparisonPrincipleToEventFlow_injective heq),
      rfl⟩

end TasteGate
end BEDC.Derived.RegularCauchyComparisonPrincipleUp
