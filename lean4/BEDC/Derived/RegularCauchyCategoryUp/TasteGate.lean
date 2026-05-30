import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCategoryUp : Type where
  | mk (O M I Q S R D E H C P N : BHist) : RegularCauchyCategoryUp
  deriving DecidableEq

def regularCauchyCategoryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCategoryEncodeBHist h

def regularCauchyCategoryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCategoryDecodeBHist tail)

private theorem regularCauchyCategory_decode_encode :
    ∀ h : BHist, regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCategoryFields : RegularCauchyCategoryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCategoryUp.mk O M I Q S R D E H C P N => [O, M, I, Q, S, R, D, E, H, C, P, N]

def regularCauchyCategoryToEventFlow : RegularCauchyCategoryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b1, BMark.b0, BMark.b1, BMark.b0] ::
        (regularCauchyCategoryFields x).map regularCauchyCategoryEncodeBHist

private def regularCauchyCategoryEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCategoryEventAt index rest

def regularCauchyCategoryFromEventFlow : EventFlow -> Option RegularCauchyCategoryUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyCategoryUp.mk
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 1 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 2 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 3 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 4 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 5 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 6 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 7 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 8 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 9 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 10 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 11 ef))
          (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEventAt 12 ef)))

private theorem regularCauchyCategory_round_trip :
    ∀ x : RegularCauchyCategoryUp,
      regularCauchyCategoryFromEventFlow (regularCauchyCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O M I Q S R D E H C P N =>
      change
        some
          (RegularCauchyCategoryUp.mk
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist O))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist M))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist I))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist Q))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist S))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist R))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist D))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist E))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist H))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist C))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist P))
            (regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist N))) =
          some (RegularCauchyCategoryUp.mk O M I Q S R D E H C P N)
      rw [regularCauchyCategory_decode_encode O, regularCauchyCategory_decode_encode M,
        regularCauchyCategory_decode_encode I, regularCauchyCategory_decode_encode Q,
        regularCauchyCategory_decode_encode S, regularCauchyCategory_decode_encode R,
        regularCauchyCategory_decode_encode D, regularCauchyCategory_decode_encode E,
        regularCauchyCategory_decode_encode H, regularCauchyCategory_decode_encode C,
        regularCauchyCategory_decode_encode P, regularCauchyCategory_decode_encode N]

private theorem regularCauchyCategoryToEventFlow_injective
    {x y : RegularCauchyCategoryUp} :
    regularCauchyCategoryToEventFlow x = regularCauchyCategoryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      regularCauchyCategoryFromEventFlow (regularCauchyCategoryToEventFlow x) =
        regularCauchyCategoryFromEventFlow (regularCauchyCategoryToEventFlow y) :=
    congrArg regularCauchyCategoryFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (regularCauchyCategory_round_trip x).symm
      (Eq.trans hread (regularCauchyCategory_round_trip y)))

private theorem regularCauchyCategoryFields_faithful :
    ∀ x y : RegularCauchyCategoryUp, regularCauchyCategoryFields x = regularCauchyCategoryFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk O1 M1 I1 Q1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 M2 I2 Q2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          change
            [O1, M1, I1, Q1, S1, R1, D1, E1, H1, C1, P1, N1] =
              [O2, M2, I2, Q2, S2, R2, D2, E2, H2, C2, P2, N2] at h
          injection h with hO t1
          injection t1 with hM t2
          injection t2 with hI t3
          injection t3 with hQ t4
          injection t4 with hS t5
          injection t5 with hR t6
          injection t6 with hD t7
          injection t7 with hE t8
          injection t8 with hH t9
          injection t9 with hC t10
          injection t10 with hP t11
          injection t11 with hN _
          subst hO
          subst hM
          subst hI
          subst hQ
          subst hS
          subst hR
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyCategoryBHistCarrier : BHistCarrier RegularCauchyCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCategoryToEventFlow
  fromEventFlow := regularCauchyCategoryFromEventFlow

instance regularCauchyCategoryChapterTasteGate : ChapterTasteGate RegularCauchyCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyCategoryFromEventFlow (regularCauchyCategoryToEventFlow x) = some x
    exact regularCauchyCategory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCategoryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCategoryChapterTasteGate

theorem RegularCauchyCategoryTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyCategoryDecodeBHist (regularCauchyCategoryEncodeBHist h) = h) ∧
      (∀ x y : RegularCauchyCategoryUp, regularCauchyCategoryFields x = regularCauchyCategoryFields y -> x = y) ∧
        (∃ x y : RegularCauchyCategoryUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyCategory_decode_encode, regularCauchyCategoryFields_faithful,
      ⟨RegularCauchyCategoryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        RegularCauchyCategoryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          injection h with hO _ _ _ _ _ _ _ _ _ _ _
          cases hO⟩⟩

end BEDC.Derived.RegularCauchyCategoryUp
