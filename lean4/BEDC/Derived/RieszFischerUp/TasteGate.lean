import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszFischerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RieszFischerUp : Type where
  | mk (W I H N M U T C P L : BHist) : RieszFischerUp
  deriving DecidableEq

def rieszFischerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszFischerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszFischerEncodeBHist h

def rieszFischerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszFischerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszFischerDecodeBHist tail)

private theorem rieszFischer_decode_encode_bhist :
    ∀ h : BHist, rieszFischerDecodeBHist (rieszFischerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def rieszFischerFields : RieszFischerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszFischerUp.mk W I H N M U T C P L => [W, I, H, N, M, U, T, C, P, L]

def rieszFischerToEventFlow : RieszFischerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rieszFischerFields x).map rieszFischerEncodeBHist

private def rieszFischerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => rieszFischerRawAt n rest

private def rieszFischerLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => rieszFischerLengthEq n rest

def rieszFischerFromEventFlow : EventFlow → Option RieszFischerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match rieszFischerLengthEq 10 flow with
      | true =>
          some
            (RieszFischerUp.mk
              (rieszFischerDecodeBHist (rieszFischerRawAt 0 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 1 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 2 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 3 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 4 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 5 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 6 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 7 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 8 flow))
              (rieszFischerDecodeBHist (rieszFischerRawAt 9 flow)))
      | false => none

private theorem rieszFischer_round_trip :
    ∀ x : RieszFischerUp,
      rieszFischerFromEventFlow (rieszFischerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W I H N M U T C P L =>
      change
        some
          (RieszFischerUp.mk
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist W))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist I))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist H))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist N))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist M))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist U))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist T))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist C))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist P))
            (rieszFischerDecodeBHist (rieszFischerEncodeBHist L))) =
          some (RieszFischerUp.mk W I H N M U T C P L)
      rw [rieszFischer_decode_encode_bhist W,
        rieszFischer_decode_encode_bhist I,
        rieszFischer_decode_encode_bhist H,
        rieszFischer_decode_encode_bhist N,
        rieszFischer_decode_encode_bhist M,
        rieszFischer_decode_encode_bhist U,
        rieszFischer_decode_encode_bhist T,
        rieszFischer_decode_encode_bhist C,
        rieszFischer_decode_encode_bhist P,
        rieszFischer_decode_encode_bhist L]

private theorem rieszFischerToEventFlow_injective {x y : RieszFischerUp} :
    rieszFischerToEventFlow x = rieszFischerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rieszFischerFromEventFlow (rieszFischerToEventFlow x) =
        rieszFischerFromEventFlow (rieszFischerToEventFlow y) :=
    congrArg rieszFischerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rieszFischer_round_trip x).symm
      (Eq.trans hread (rieszFischer_round_trip y)))

instance rieszFischerBHistCarrier : BHistCarrier RieszFischerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszFischerToEventFlow
  fromEventFlow := rieszFischerFromEventFlow

instance rieszFischerChapterTasteGate : ChapterTasteGate RieszFischerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rieszFischerFromEventFlow (rieszFischerToEventFlow x) = some x
    exact rieszFischer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rieszFischerToEventFlow_injective heq)

theorem RieszFischerTasteGate_single_carrier_alignment :
    (∀ h : BHist, rieszFischerDecodeBHist (rieszFischerEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RieszFischerUp) ∧
        Nonempty (ChapterTasteGate RieszFischerUp) ∧
          rieszFischerFields
              (RieszFischerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rieszFischer_decode_encode_bhist,
      ⟨rieszFischerBHistCarrier⟩,
      ⟨rieszFischerChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RieszFischerUp
