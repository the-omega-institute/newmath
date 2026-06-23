import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusFunctorUp : Type where
  | mk (D S R E A T H C P N : BHist) : CauchyModulusFunctorUp

def cauchyModulusFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusFunctorEncodeBHist h

def cauchyModulusFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusFunctorDecodeBHist tail)

private theorem cauchyModulusFunctorDecodeEncode :
    ∀ h : BHist,
      cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusFunctorFields : CauchyModulusFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusFunctorUp.mk D S R E A T H C P N => [D, S, R, E, A, T, H, C, P, N]

def cauchyModulusFunctorToEventFlow : CauchyModulusFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusFunctorFields x).map cauchyModulusFunctorEncodeBHist

private def cauchyModulusFunctorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusFunctorEventAt index rest

def cauchyModulusFunctorFromEventFlow
    (ef : EventFlow) : Option CauchyModulusFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusFunctorUp.mk
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 0 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 1 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 2 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 3 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 4 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 5 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 6 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 7 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 8 ef))
      (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEventAt 9 ef)))

private theorem cauchyModulusFunctorRoundTrip (x : CauchyModulusFunctorUp) :
    cauchyModulusFunctorFromEventFlow (cauchyModulusFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R E A T H C P N =>
      change
        some
          (CauchyModulusFunctorUp.mk
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist D))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist S))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist R))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist E))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist A))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist T))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist H))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist C))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist P))
            (cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist N))) =
          some (CauchyModulusFunctorUp.mk D S R E A T H C P N)
      rw [cauchyModulusFunctorDecodeEncode D, cauchyModulusFunctorDecodeEncode S,
        cauchyModulusFunctorDecodeEncode R, cauchyModulusFunctorDecodeEncode E,
        cauchyModulusFunctorDecodeEncode A, cauchyModulusFunctorDecodeEncode T,
        cauchyModulusFunctorDecodeEncode H, cauchyModulusFunctorDecodeEncode C,
        cauchyModulusFunctorDecodeEncode P, cauchyModulusFunctorDecodeEncode N]

private theorem cauchyModulusFunctorToEventFlow_injective
    {x y : CauchyModulusFunctorUp} :
    cauchyModulusFunctorToEventFlow x = cauchyModulusFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusFunctorFromEventFlow (cauchyModulusFunctorToEventFlow x) =
        cauchyModulusFunctorFromEventFlow (cauchyModulusFunctorToEventFlow y) :=
    congrArg cauchyModulusFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusFunctorRoundTrip x).symm
      (Eq.trans hread (cauchyModulusFunctorRoundTrip y)))

instance cauchyModulusFunctorBHistCarrier : BHistCarrier CauchyModulusFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusFunctorToEventFlow
  fromEventFlow := cauchyModulusFunctorFromEventFlow

instance cauchyModulusFunctorChapterTasteGate :
    ChapterTasteGate CauchyModulusFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusFunctorFromEventFlow (cauchyModulusFunctorToEventFlow x) = some x
    exact cauchyModulusFunctorRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusFunctorToEventFlow_injective heq)

theorem CauchyModulusFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyModulusFunctorDecodeBHist (cauchyModulusFunctorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyModulusFunctorUp) ∧
        Nonempty (ChapterTasteGate CauchyModulusFunctorUp) ∧
          cauchyModulusFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyModulusFunctorDecodeEncode, ⟨cauchyModulusFunctorBHistCarrier⟩,
      ⟨cauchyModulusFunctorChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyModulusFunctorUp
