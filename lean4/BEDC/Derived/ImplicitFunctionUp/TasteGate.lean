import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ImplicitFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ImplicitFunctionUp : Type where
  | mk (E B D L M Q G R H C P N : BHist) : ImplicitFunctionUp
  deriving DecidableEq

def implicitFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: implicitFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: implicitFunctionEncodeBHist h

def implicitFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (implicitFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (implicitFunctionDecodeBHist tail)

private theorem ImplicitFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, implicitFunctionDecodeBHist (implicitFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def implicitFunctionToEventFlow : ImplicitFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ImplicitFunctionUp.mk E B D L M Q G R H C P N =>
      [[BMark.b0],
        implicitFunctionEncodeBHist E,
        [BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        implicitFunctionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        implicitFunctionEncodeBHist N]

private def implicitFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => implicitFunctionEventAtDefault index rest

def implicitFunctionFromEventFlow (ef : EventFlow) : Option ImplicitFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ImplicitFunctionUp.mk
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 1 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 3 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 5 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 7 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 9 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 11 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 13 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 15 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 17 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 19 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 21 ef))
      (implicitFunctionDecodeBHist (implicitFunctionEventAtDefault 23 ef)))

private theorem ImplicitFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ImplicitFunctionUp,
      implicitFunctionFromEventFlow (implicitFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E B D L M Q G R H C P N =>
      change
        some
          (ImplicitFunctionUp.mk
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist E))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist B))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist D))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist L))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist M))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist Q))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist G))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist R))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist H))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist C))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist P))
            (implicitFunctionDecodeBHist (implicitFunctionEncodeBHist N))) =
          some (ImplicitFunctionUp.mk E B D L M Q G R H C P N)
      rw [ImplicitFunctionTasteGate_single_carrier_alignment_decode E,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode B,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode D,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode L,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode M,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode Q,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode G,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode R,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode H,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode C,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode P,
        ImplicitFunctionTasteGate_single_carrier_alignment_decode N]

private theorem ImplicitFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ImplicitFunctionUp} :
    implicitFunctionToEventFlow x = implicitFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      implicitFunctionFromEventFlow (implicitFunctionToEventFlow x) =
        implicitFunctionFromEventFlow (implicitFunctionToEventFlow y) :=
    congrArg implicitFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ImplicitFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ImplicitFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance implicitFunctionBHistCarrier : BHistCarrier ImplicitFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := implicitFunctionToEventFlow
  fromEventFlow := implicitFunctionFromEventFlow

instance implicitFunctionChapterTasteGate : ChapterTasteGate ImplicitFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change implicitFunctionFromEventFlow (implicitFunctionToEventFlow x) = some x
    exact ImplicitFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ImplicitFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ImplicitFunctionTasteGate_single_carrier_alignment :
    (forall h : BHist, implicitFunctionDecodeBHist (implicitFunctionEncodeBHist h) = h) /\
      (forall x : ImplicitFunctionUp,
        implicitFunctionFromEventFlow (implicitFunctionToEventFlow x) = some x) /\
      (forall x y : ImplicitFunctionUp,
        implicitFunctionToEventFlow x = implicitFunctionToEventFlow y -> x = y) /\
      implicitFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ImplicitFunctionTasteGate_single_carrier_alignment_decode,
      ImplicitFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ImplicitFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ImplicitFunctionUp
