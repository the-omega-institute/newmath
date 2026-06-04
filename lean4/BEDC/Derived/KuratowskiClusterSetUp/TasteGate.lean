import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiClusterSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiClusterSetUp : Type where
  | mk (S F Kh Km C M B X R E T U P N : BHist) : KuratowskiClusterSetUp
  deriving DecidableEq

def kuratowskiClusterSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiClusterSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiClusterSetEncodeBHist h

def kuratowskiClusterSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiClusterSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiClusterSetDecodeBHist tail)

private theorem KuratowskiClusterSetUp_decode :
    ∀ h : BHist,
      kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiClusterSetFields : KuratowskiClusterSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N =>
      [S, F, Kh, Km, C, M, B, X, R, E, T, U, P, N]

def kuratowskiClusterSetToEventFlow : KuratowskiClusterSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (kuratowskiClusterSetFields x).map kuratowskiClusterSetEncodeBHist

private def kuratowskiClusterSetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiClusterSetEventAtDefault index rest

def kuratowskiClusterSetFromEventFlow
    (ef : EventFlow) : Option KuratowskiClusterSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiClusterSetUp.mk
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 0 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 1 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 2 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 3 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 4 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 5 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 6 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 7 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 8 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 9 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 10 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 11 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 12 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 13 ef)))

private theorem KuratowskiClusterSetUp_round_trip (x : KuratowskiClusterSetUp) :
    kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S F Kh Km C M B X R E T U P N =>
      change
        some
          (KuratowskiClusterSetUp.mk
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist S))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist F))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist Kh))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist Km))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist C))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist M))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist B))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist X))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist R))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist E))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist T))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist U))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist P))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist N))) =
          some (KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N)
      rw [KuratowskiClusterSetUp_decode S, KuratowskiClusterSetUp_decode F,
        KuratowskiClusterSetUp_decode Kh, KuratowskiClusterSetUp_decode Km,
        KuratowskiClusterSetUp_decode C, KuratowskiClusterSetUp_decode M,
        KuratowskiClusterSetUp_decode B, KuratowskiClusterSetUp_decode X,
        KuratowskiClusterSetUp_decode R, KuratowskiClusterSetUp_decode E,
        KuratowskiClusterSetUp_decode T, KuratowskiClusterSetUp_decode U,
        KuratowskiClusterSetUp_decode P, KuratowskiClusterSetUp_decode N]

private theorem KuratowskiClusterSetUp_toEventFlow_injective
    {x y : KuratowskiClusterSetUp} :
    kuratowskiClusterSetToEventFlow x = kuratowskiClusterSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) =
        kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow y) :=
    congrArg kuratowskiClusterSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KuratowskiClusterSetUp_round_trip x).symm
      (Eq.trans hread (KuratowskiClusterSetUp_round_trip y)))

private theorem KuratowskiClusterSetUp_fields :
    ∀ x y : KuratowskiClusterSetUp,
      kuratowskiClusterSetFields x = kuratowskiClusterSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 F1 Kh1 Km1 C1 M1 B1 X1 R1 E1 T1 U1 P1 N1 =>
      cases y with
      | mk S2 F2 Kh2 Km2 C2 M2 B2 X2 R2 E2 T2 U2 P2 N2 =>
          cases hfields
          rfl

instance kuratowskiClusterSetBHistCarrier :
    BHistCarrier KuratowskiClusterSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiClusterSetToEventFlow
  fromEventFlow := kuratowskiClusterSetFromEventFlow

instance kuratowskiClusterSetChapterTasteGate :
    ChapterTasteGate KuratowskiClusterSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) = some x
    exact KuratowskiClusterSetUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KuratowskiClusterSetUp_toEventFlow_injective heq)

instance kuratowskiClusterSetFieldFaithful :
    FieldFaithful KuratowskiClusterSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kuratowskiClusterSetFields
  field_faithful := KuratowskiClusterSetUp_fields

def taste_gate : ChapterTasteGate KuratowskiClusterSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kuratowskiClusterSetChapterTasteGate

theorem KuratowskiClusterSetTasteGate_single_carrier_alignment
    (x : KuratowskiClusterSetUp) :
    (∃ S F Kh Km C M B X R E T U P N : BHist,
      x = KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N ∧
        kuratowskiClusterSetFields x = [S, F, Kh, Km, C, M, B, X, R, E, T, U, P, N]) ∧
      kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) = some x ∧
        kuratowskiClusterSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S F Kh Km C M B X R E T U P N =>
      exact
        ⟨⟨S, F, Kh, Km, C, M, B, X, R, E, T, U, P, N, rfl, rfl⟩,
          KuratowskiClusterSetUp_round_trip
            (KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N),
          rfl⟩

end BEDC.Derived.KuratowskiClusterSetUp
