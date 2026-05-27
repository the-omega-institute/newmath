import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanCauchyTailUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanCauchyTailUp : Type where
  | mk (R A M E W Q D H C P N : BHist) : ArchimedeanCauchyTailUp
  deriving DecidableEq

def archimedeanCauchyTailEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanCauchyTailEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanCauchyTailEncodeBHist h

def archimedeanCauchyTailDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanCauchyTailDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanCauchyTailDecodeBHist tail)

private theorem ArchimedeanCauchyTailTasteGate_decode_encode :
    ∀ h : BHist, archimedeanCauchyTailDecodeBHist
      (archimedeanCauchyTailEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanCauchyTailFields : ArchimedeanCauchyTailUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanCauchyTailUp.mk R A M E W Q D H C P N => [R, A, M, E, W, Q, D, H, C, P, N]

def archimedeanCauchyTailToEventFlow : ArchimedeanCauchyTailUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => archimedeanCauchyTailFields x |>.map archimedeanCauchyTailEncodeBHist

private def archimedeanCauchyTailEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => archimedeanCauchyTailEventAt index rest

def archimedeanCauchyTailFromEventFlow
    (ef : EventFlow) : Option ArchimedeanCauchyTailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArchimedeanCauchyTailUp.mk
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 0 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 1 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 2 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 3 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 4 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 5 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 6 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 7 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 8 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 9 ef))
      (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEventAt 10 ef)))

private theorem ArchimedeanCauchyTailTasteGate_round_trip
    (x : ArchimedeanCauchyTailUp) :
    archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R A M E W Q D H C P N =>
      change
        some
          (ArchimedeanCauchyTailUp.mk
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist R))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist A))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist M))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist E))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist W))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist Q))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist D))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist H))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist C))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist P))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist N))) =
          some (ArchimedeanCauchyTailUp.mk R A M E W Q D H C P N)
      rw [ArchimedeanCauchyTailTasteGate_decode_encode R,
        ArchimedeanCauchyTailTasteGate_decode_encode A,
        ArchimedeanCauchyTailTasteGate_decode_encode M,
        ArchimedeanCauchyTailTasteGate_decode_encode E,
        ArchimedeanCauchyTailTasteGate_decode_encode W,
        ArchimedeanCauchyTailTasteGate_decode_encode Q,
        ArchimedeanCauchyTailTasteGate_decode_encode D,
        ArchimedeanCauchyTailTasteGate_decode_encode H,
        ArchimedeanCauchyTailTasteGate_decode_encode C,
        ArchimedeanCauchyTailTasteGate_decode_encode P,
        ArchimedeanCauchyTailTasteGate_decode_encode N]

private theorem ArchimedeanCauchyTailTasteGate_toEventFlow_injective
    {x y : ArchimedeanCauchyTailUp} :
    archimedeanCauchyTailToEventFlow x = archimedeanCauchyTailToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow x) =
        archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow y) :=
    congrArg archimedeanCauchyTailFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArchimedeanCauchyTailTasteGate_round_trip x).symm
      (Eq.trans hread (ArchimedeanCauchyTailTasteGate_round_trip y)))

private theorem ArchimedeanCauchyTailTasteGate_fields_faithful :
    ∀ x y : ArchimedeanCauchyTailUp,
      archimedeanCauchyTailFields x = archimedeanCauchyTailFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ A₁ M₁ E₁ W₁ Q₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ A₂ M₂ E₂ W₂ Q₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance archimedeanCauchyTailBHistCarrier :
    BHistCarrier ArchimedeanCauchyTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanCauchyTailToEventFlow
  fromEventFlow := archimedeanCauchyTailFromEventFlow

instance archimedeanCauchyTailChapterTasteGate :
    ChapterTasteGate ArchimedeanCauchyTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow x) =
        some x
    exact ArchimedeanCauchyTailTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanCauchyTailTasteGate_toEventFlow_injective heq)

instance archimedeanCauchyTailFieldFaithful :
    FieldFaithful ArchimedeanCauchyTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanCauchyTailFields
  field_faithful := ArchimedeanCauchyTailTasteGate_fields_faithful

def taste_gate : ChapterTasteGate ArchimedeanCauchyTailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanCauchyTailChapterTasteGate

theorem ArchimedeanCauchyTailTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ArchimedeanCauchyTailUp) ∧
      Nonempty (ChapterTasteGate ArchimedeanCauchyTailUp) ∧
        (∀ h : BHist,
          archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist h) = h) ∧
          archimedeanCauchyTailEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨archimedeanCauchyTailBHistCarrier⟩,
      ⟨archimedeanCauchyTailChapterTasteGate⟩,
      ArchimedeanCauchyTailTasteGate_decode_encode,
      rfl⟩

end BEDC.Derived.ArchimedeanCauchyTailUp
