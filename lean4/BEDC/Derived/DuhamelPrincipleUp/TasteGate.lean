import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DuhamelPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DuhamelPrincipleUp : Type where
  | mk (T E F G I S H C P N : BHist) : DuhamelPrincipleUp
  deriving DecidableEq

def duhamelPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: duhamelPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: duhamelPrincipleEncodeBHist h

def duhamelPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (duhamelPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (duhamelPrincipleDecodeBHist tail)

private theorem DuhamelPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def duhamelPrincipleFields : DuhamelPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DuhamelPrincipleUp.mk T E F G I S H C P N => [T, E, F, G, I, S, H, C, P, N]

def duhamelPrincipleToEventFlow : DuhamelPrincipleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (duhamelPrincipleFields x).map duhamelPrincipleEncodeBHist

private def duhamelPrincipleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => duhamelPrincipleEventAtDefault index rest

def duhamelPrincipleFromEventFlow (ef : EventFlow) : Option DuhamelPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DuhamelPrincipleUp.mk
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 0 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 1 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 2 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 3 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 4 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 5 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 6 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 7 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 8 ef))
      (duhamelPrincipleDecodeBHist (duhamelPrincipleEventAtDefault 9 ef)))

private theorem duhamelPrinciple_round_trip :
    ∀ x : DuhamelPrincipleUp,
      duhamelPrincipleFromEventFlow (duhamelPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T E F G I S H C P N =>
      change
        some
          (DuhamelPrincipleUp.mk
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist T))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist E))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist F))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist G))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist I))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist S))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist H))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist C))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist P))
            (duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist N))) =
          some (DuhamelPrincipleUp.mk T E F G I S H C P N)
      rw [DuhamelPrincipleTasteGate_single_carrier_alignment_decode T,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode E,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode F,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode G,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode I,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode S,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode H,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode C,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode P,
        DuhamelPrincipleTasteGate_single_carrier_alignment_decode N]

private theorem DuhamelPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DuhamelPrincipleUp} :
    duhamelPrincipleToEventFlow x = duhamelPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      duhamelPrincipleFromEventFlow (duhamelPrincipleToEventFlow x) =
        duhamelPrincipleFromEventFlow (duhamelPrincipleToEventFlow y) :=
    congrArg duhamelPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (duhamelPrinciple_round_trip x).symm
      (Eq.trans hread (duhamelPrinciple_round_trip y)))

instance duhamelPrincipleBHistCarrier : BHistCarrier DuhamelPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := duhamelPrincipleToEventFlow
  fromEventFlow := duhamelPrincipleFromEventFlow

instance duhamelPrincipleChapterTasteGate : ChapterTasteGate DuhamelPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change duhamelPrincipleFromEventFlow (duhamelPrincipleToEventFlow x) = some x
    exact duhamelPrinciple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DuhamelPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DuhamelPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  duhamelPrincipleChapterTasteGate

theorem DuhamelPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist, duhamelPrincipleDecodeBHist (duhamelPrincipleEncodeBHist h) = h) ∧
      (∀ x : DuhamelPrincipleUp,
        duhamelPrincipleFromEventFlow (duhamelPrincipleToEventFlow x) = some x) ∧
        (∀ x y : DuhamelPrincipleUp,
          duhamelPrincipleToEventFlow x = duhamelPrincipleToEventFlow y → x = y) ∧
          duhamelPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DuhamelPrincipleTasteGate_single_carrier_alignment_decode,
      duhamelPrinciple_round_trip,
      fun _x _y => DuhamelPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.DuhamelPrincipleUp
