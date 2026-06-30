import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICResidualSubstitutionCompatibilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICResidualSubstitutionCompatibilityUp : Type where
  | mk (s t b j g a h c p n : BHist) : MetaCICResidualSubstitutionCompatibilityUp
  deriving DecidableEq

def metaCICResidualSubstitutionCompatibilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICResidualSubstitutionCompatibilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICResidualSubstitutionCompatibilityEncodeBHist h

def metaCICResidualSubstitutionCompatibilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICResidualSubstitutionCompatibilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICResidualSubstitutionCompatibilityDecodeBHist tail)

private theorem metaCICResidualSubstitutionCompatibility_decode_encode :
    ∀ h : BHist,
      metaCICResidualSubstitutionCompatibilityDecodeBHist
          (metaCICResidualSubstitutionCompatibilityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICResidualSubstitutionCompatibilityFields :
    MetaCICResidualSubstitutionCompatibilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICResidualSubstitutionCompatibilityUp.mk s t b j g a h c p n =>
      [s, t, b, j, g, a, h, c, p, n]

def metaCICResidualSubstitutionCompatibilityToEventFlow :
    MetaCICResidualSubstitutionCompatibilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metaCICResidualSubstitutionCompatibilityFields x).map
        metaCICResidualSubstitutionCompatibilityEncodeBHist

private def metaCICResidualSubstitutionCompatibilityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICResidualSubstitutionCompatibilityEventAt index rest

def metaCICResidualSubstitutionCompatibilityFromEventFlow
    (ef : EventFlow) : Option MetaCICResidualSubstitutionCompatibilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICResidualSubstitutionCompatibilityUp.mk
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 0 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 1 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 2 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 3 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 4 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 5 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 6 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 7 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 8 ef))
      (metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEventAt 9 ef)))

private theorem metaCICResidualSubstitutionCompatibility_round_trip
    (x : MetaCICResidualSubstitutionCompatibilityUp) :
    metaCICResidualSubstitutionCompatibilityFromEventFlow
        (metaCICResidualSubstitutionCompatibilityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk s t b j g a h c p n =>
      change
        some
          (MetaCICResidualSubstitutionCompatibilityUp.mk
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist s))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist t))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist b))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist j))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist g))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist a))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist h))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist c))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist p))
            (metaCICResidualSubstitutionCompatibilityDecodeBHist
              (metaCICResidualSubstitutionCompatibilityEncodeBHist n))) =
          some (MetaCICResidualSubstitutionCompatibilityUp.mk s t b j g a h c p n)
      rw [metaCICResidualSubstitutionCompatibility_decode_encode s,
        metaCICResidualSubstitutionCompatibility_decode_encode t,
        metaCICResidualSubstitutionCompatibility_decode_encode b,
        metaCICResidualSubstitutionCompatibility_decode_encode j,
        metaCICResidualSubstitutionCompatibility_decode_encode g,
        metaCICResidualSubstitutionCompatibility_decode_encode a,
        metaCICResidualSubstitutionCompatibility_decode_encode h,
        metaCICResidualSubstitutionCompatibility_decode_encode c,
        metaCICResidualSubstitutionCompatibility_decode_encode p,
        metaCICResidualSubstitutionCompatibility_decode_encode n]

private theorem metaCICResidualSubstitutionCompatibilityToEventFlow_injective
    {x y : MetaCICResidualSubstitutionCompatibilityUp} :
    metaCICResidualSubstitutionCompatibilityToEventFlow x =
        metaCICResidualSubstitutionCompatibilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICResidualSubstitutionCompatibilityFromEventFlow
          (metaCICResidualSubstitutionCompatibilityToEventFlow x) =
        metaCICResidualSubstitutionCompatibilityFromEventFlow
          (metaCICResidualSubstitutionCompatibilityToEventFlow y) :=
    congrArg metaCICResidualSubstitutionCompatibilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICResidualSubstitutionCompatibility_round_trip x).symm
      (Eq.trans hread (metaCICResidualSubstitutionCompatibility_round_trip y)))

instance metaCICResidualSubstitutionCompatibilityBHistCarrier :
    BHistCarrier MetaCICResidualSubstitutionCompatibilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICResidualSubstitutionCompatibilityToEventFlow
  fromEventFlow := metaCICResidualSubstitutionCompatibilityFromEventFlow

instance metaCICResidualSubstitutionCompatibilityChapterTasteGate :
    ChapterTasteGate MetaCICResidualSubstitutionCompatibilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICResidualSubstitutionCompatibilityFromEventFlow
          (metaCICResidualSubstitutionCompatibilityToEventFlow x) =
        some x
    exact metaCICResidualSubstitutionCompatibility_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICResidualSubstitutionCompatibilityToEventFlow_injective heq)

theorem MetaCICResidualSubstitutionCompatibilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICResidualSubstitutionCompatibilityDecodeBHist
        (metaCICResidualSubstitutionCompatibilityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetaCICResidualSubstitutionCompatibilityUp) ∧
        Nonempty (ChapterTasteGate MetaCICResidualSubstitutionCompatibilityUp) ∧
          metaCICResidualSubstitutionCompatibilityEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨metaCICResidualSubstitutionCompatibility_decode_encode,
      ⟨metaCICResidualSubstitutionCompatibilityBHistCarrier⟩,
      ⟨metaCICResidualSubstitutionCompatibilityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetaCICResidualSubstitutionCompatibilityUp
