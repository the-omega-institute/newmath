import BEDC.Derived.PoincareInequalityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def poincareInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareInequalityEncodeBHist h

def poincareInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareInequalityDecodeBHist tail)

private theorem PoincareInequalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      poincareInequalityDecodeBHist (poincareInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def poincareInequalityFields :
    BEDC.Derived.PoincareInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareInequalityUp.mk domain boundary gradient norm constant transport replay provenance name =>
      [domain, boundary, gradient, norm, constant, transport, replay, provenance, name]

def poincareInequalityToEventFlow :
    BEDC.Derived.PoincareInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareInequalityFields x).map poincareInequalityEncodeBHist

private def poincareInequalityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => poincareInequalityEventAt index rest

def poincareInequalityFromEventFlow :
    EventFlow → Option BEDC.Derived.PoincareInequalityUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PoincareInequalityUp.mk
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 0 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 1 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 2 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 3 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 4 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 5 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 6 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 7 ef))
          (poincareInequalityDecodeBHist (poincareInequalityEventAt 8 ef)))

private theorem PoincareInequalityTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.PoincareInequalityUp) :
    poincareInequalityFromEventFlow (poincareInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk domain boundary gradient norm constant transport replay provenance name =>
      change
        some
          (PoincareInequalityUp.mk
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist domain))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist boundary))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist gradient))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist norm))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist constant))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist transport))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist replay))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist provenance))
            (poincareInequalityDecodeBHist (poincareInequalityEncodeBHist name))) =
          some
            (PoincareInequalityUp.mk domain boundary gradient norm constant transport replay
              provenance name)
      rw [PoincareInequalityTasteGate_single_carrier_alignment_decode_encode domain,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode boundary,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode gradient,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode norm,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode constant,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode transport,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode replay,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode provenance,
        PoincareInequalityTasteGate_single_carrier_alignment_decode_encode name]

private theorem PoincareInequalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.PoincareInequalityUp} :
    poincareInequalityToEventFlow x = poincareInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareInequalityFromEventFlow (poincareInequalityToEventFlow x) =
        poincareInequalityFromEventFlow (poincareInequalityToEventFlow y) :=
    congrArg poincareInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PoincareInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PoincareInequalityTasteGate_single_carrier_alignment_round_trip y)))

instance poincareInequalityBHistCarrier :
    BHistCarrier BEDC.Derived.PoincareInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareInequalityToEventFlow
  fromEventFlow := poincareInequalityFromEventFlow

instance poincareInequalityChapterTasteGate :
    ChapterTasteGate BEDC.Derived.PoincareInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change poincareInequalityFromEventFlow (poincareInequalityToEventFlow x) = some x
    exact PoincareInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PoincareInequalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PoincareInequalityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BEDC.Derived.PoincareInequalityUp) ∧
      (∀ h : BHist,
        poincareInequalityDecodeBHist (poincareInequalityEncodeBHist h) = h) ∧
        poincareInequalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨poincareInequalityChapterTasteGate⟩,
      PoincareInequalityTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.PoincareInequalityUp
