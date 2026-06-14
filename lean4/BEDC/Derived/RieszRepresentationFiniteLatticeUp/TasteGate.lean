import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszRepresentationFiniteLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RieszRepresentationFiniteLatticeUp : Type where
  | mk (L O F A B P H C N : BHist) : RieszRepresentationFiniteLatticeUp
  deriving DecidableEq

def rieszRepresentationFiniteLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszRepresentationFiniteLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszRepresentationFiniteLatticeEncodeBHist h

def rieszRepresentationFiniteLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszRepresentationFiniteLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszRepresentationFiniteLatticeDecodeBHist tail)

private theorem rieszRepresentationFiniteLatticeDecodeEncode :
    ∀ h : BHist,
      rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def rieszRepresentationFiniteLatticeFields :
    RieszRepresentationFiniteLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszRepresentationFiniteLatticeUp.mk L O F A B P H C N => [L, O, F, A, B, P, H, C, N]

def rieszRepresentationFiniteLatticeToEventFlow :
    RieszRepresentationFiniteLatticeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (rieszRepresentationFiniteLatticeFields x).map
      rieszRepresentationFiniteLatticeEncodeBHist

private def rieszRepresentationFiniteLatticeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      rieszRepresentationFiniteLatticeEventAtDefault index rest

def rieszRepresentationFiniteLatticeFromEventFlow
    (ef : EventFlow) : Option RieszRepresentationFiniteLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RieszRepresentationFiniteLatticeUp.mk
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 0 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 1 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 2 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 3 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 4 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 5 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 6 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 7 ef))
      (rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEventAtDefault 8 ef)))

private theorem rieszRepresentationFiniteLatticeRoundTrip :
    ∀ x : RieszRepresentationFiniteLatticeUp,
      rieszRepresentationFiniteLatticeFromEventFlow
        (rieszRepresentationFiniteLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L O F A B P H C N =>
      change
        some
          (RieszRepresentationFiniteLatticeUp.mk
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist L))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist O))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist F))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist A))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist B))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist P))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist H))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist C))
            (rieszRepresentationFiniteLatticeDecodeBHist
              (rieszRepresentationFiniteLatticeEncodeBHist N))) =
          some (RieszRepresentationFiniteLatticeUp.mk L O F A B P H C N)
      rw [rieszRepresentationFiniteLatticeDecodeEncode L,
        rieszRepresentationFiniteLatticeDecodeEncode O,
        rieszRepresentationFiniteLatticeDecodeEncode F,
        rieszRepresentationFiniteLatticeDecodeEncode A,
        rieszRepresentationFiniteLatticeDecodeEncode B,
        rieszRepresentationFiniteLatticeDecodeEncode P,
        rieszRepresentationFiniteLatticeDecodeEncode H,
        rieszRepresentationFiniteLatticeDecodeEncode C,
        rieszRepresentationFiniteLatticeDecodeEncode N]

private theorem rieszRepresentationFiniteLatticeToEventFlow_injective
    {x y : RieszRepresentationFiniteLatticeUp} :
    rieszRepresentationFiniteLatticeToEventFlow x =
      rieszRepresentationFiniteLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rieszRepresentationFiniteLatticeFromEventFlow
          (rieszRepresentationFiniteLatticeToEventFlow x) =
        rieszRepresentationFiniteLatticeFromEventFlow
          (rieszRepresentationFiniteLatticeToEventFlow y) :=
    congrArg rieszRepresentationFiniteLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rieszRepresentationFiniteLatticeRoundTrip x).symm
      (Eq.trans hread (rieszRepresentationFiniteLatticeRoundTrip y)))

instance rieszRepresentationFiniteLatticeBHistCarrier :
    BHistCarrier RieszRepresentationFiniteLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszRepresentationFiniteLatticeToEventFlow
  fromEventFlow := rieszRepresentationFiniteLatticeFromEventFlow

instance rieszRepresentationFiniteLatticeChapterTasteGate :
    ChapterTasteGate RieszRepresentationFiniteLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rieszRepresentationFiniteLatticeFromEventFlow
        (rieszRepresentationFiniteLatticeToEventFlow x) = some x
    exact rieszRepresentationFiniteLatticeRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rieszRepresentationFiniteLatticeToEventFlow_injective heq)

theorem RieszRepresentationFiniteLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rieszRepresentationFiniteLatticeDecodeBHist
        (rieszRepresentationFiniteLatticeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RieszRepresentationFiniteLatticeUp) ∧
        Nonempty (ChapterTasteGate RieszRepresentationFiniteLatticeUp) ∧
          rieszRepresentationFiniteLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rieszRepresentationFiniteLatticeDecodeEncode,
      ⟨rieszRepresentationFiniteLatticeBHistCarrier⟩,
      ⟨rieszRepresentationFiniteLatticeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RieszRepresentationFiniteLatticeUp
