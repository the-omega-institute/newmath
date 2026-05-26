import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyScalarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyScalarUp : Type where
  | mk (X A W D F E H C P N : BHist) : RegularCauchyScalarUp
  deriving DecidableEq

def regularCauchyScalarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyScalarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyScalarEncodeBHist h

def regularCauchyScalarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyScalarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyScalarDecodeBHist tail)

private theorem regularCauchyScalar_decode_encode :
    ∀ h : BHist, regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyScalarFields : RegularCauchyScalarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyScalarUp.mk X A W D F E H C P N => [X, A, W, D, F, E, H, C, P, N]

def regularCauchyScalarToEventFlow : RegularCauchyScalarUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b0, BMark.b1, BMark.b0] ::
        (regularCauchyScalarFields x).map regularCauchyScalarEncodeBHist

private def regularCauchyScalarEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyScalarEventAt index rest

def regularCauchyScalarFromEventFlow : EventFlow → Option RegularCauchyScalarUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyScalarUp.mk
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 1 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 2 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 3 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 4 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 5 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 6 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 7 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 8 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 9 ef))
          (regularCauchyScalarDecodeBHist (regularCauchyScalarEventAt 10 ef)))

private theorem regularCauchyScalar_round_trip :
    ∀ x : RegularCauchyScalarUp,
      regularCauchyScalarFromEventFlow (regularCauchyScalarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A W D F E H C P N =>
      change
        some
          (RegularCauchyScalarUp.mk
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist X))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist A))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist W))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist D))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist F))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist E))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist H))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist C))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist P))
            (regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist N))) =
          some (RegularCauchyScalarUp.mk X A W D F E H C P N)
      rw [regularCauchyScalar_decode_encode X, regularCauchyScalar_decode_encode A,
        regularCauchyScalar_decode_encode W, regularCauchyScalar_decode_encode D,
        regularCauchyScalar_decode_encode F, regularCauchyScalar_decode_encode E,
        regularCauchyScalar_decode_encode H, regularCauchyScalar_decode_encode C,
        regularCauchyScalar_decode_encode P, regularCauchyScalar_decode_encode N]

private theorem regularCauchyScalarToEventFlow_injective {x y : RegularCauchyScalarUp} :
    regularCauchyScalarToEventFlow x = regularCauchyScalarToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      regularCauchyScalarFromEventFlow (regularCauchyScalarToEventFlow x) =
        regularCauchyScalarFromEventFlow (regularCauchyScalarToEventFlow y) :=
    congrArg regularCauchyScalarFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (regularCauchyScalar_round_trip x).symm
      (Eq.trans hread (regularCauchyScalar_round_trip y)))

instance regularCauchyScalarBHistCarrier : BHistCarrier RegularCauchyScalarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyScalarToEventFlow
  fromEventFlow := regularCauchyScalarFromEventFlow

instance regularCauchyScalarChapterTasteGate : ChapterTasteGate RegularCauchyScalarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyScalarFromEventFlow (regularCauchyScalarToEventFlow x) = some x
    exact regularCauchyScalar_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyScalarToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyScalarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyScalarChapterTasteGate

theorem RegularCauchyScalarTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyScalarDecodeBHist (regularCauchyScalarEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyScalarUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyScalarUp) ∧
          regularCauchyScalarEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyScalar_decode_encode
  constructor
  · exact ⟨regularCauchyScalarBHistCarrier⟩
  constructor
  · exact ⟨regularCauchyScalarChapterTasteGate⟩
  · rfl

end BEDC.Derived.RegularCauchyScalarUp
