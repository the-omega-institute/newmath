import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SemiringUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SemiringUp : Type where
  | mk (A M Z D E H C P N : BHist) : SemiringUp
  deriving DecidableEq

def semiringEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: semiringEncodeBHist h
  | BHist.e1 h => BMark.b1 :: semiringEncodeBHist h

def semiringDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (semiringDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (semiringDecodeBHist tail)

private theorem semiring_decode_encode :
    ∀ h : BHist, semiringDecodeBHist (semiringEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def semiringFields : SemiringUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | SemiringUp.mk A M Z D E H C P N => [A, M, Z, D, E, H, C, P, N]

def semiringToEventFlow : SemiringUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | SemiringUp.mk A M Z D E H C P N =>
      [semiringEncodeBHist A,
        semiringEncodeBHist M,
        semiringEncodeBHist Z,
        semiringEncodeBHist D,
        semiringEncodeBHist E,
        semiringEncodeBHist H,
        semiringEncodeBHist C,
        semiringEncodeBHist P,
        semiringEncodeBHist N]

private def semiringEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => semiringEventAt index rest

def semiringFromEventFlow : EventFlow → Option SemiringUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SemiringUp.mk
        (semiringDecodeBHist (semiringEventAt 0 ef))
        (semiringDecodeBHist (semiringEventAt 1 ef))
        (semiringDecodeBHist (semiringEventAt 2 ef))
        (semiringDecodeBHist (semiringEventAt 3 ef))
        (semiringDecodeBHist (semiringEventAt 4 ef))
        (semiringDecodeBHist (semiringEventAt 5 ef))
        (semiringDecodeBHist (semiringEventAt 6 ef))
        (semiringDecodeBHist (semiringEventAt 7 ef))
        (semiringDecodeBHist (semiringEventAt 8 ef)))

private theorem semiring_round_trip :
    ∀ x : SemiringUp,
      semiringFromEventFlow (semiringToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M Z D E H C P N =>
      change
        some
          (SemiringUp.mk
            (semiringDecodeBHist (semiringEncodeBHist A))
            (semiringDecodeBHist (semiringEncodeBHist M))
            (semiringDecodeBHist (semiringEncodeBHist Z))
            (semiringDecodeBHist (semiringEncodeBHist D))
            (semiringDecodeBHist (semiringEncodeBHist E))
            (semiringDecodeBHist (semiringEncodeBHist H))
            (semiringDecodeBHist (semiringEncodeBHist C))
            (semiringDecodeBHist (semiringEncodeBHist P))
            (semiringDecodeBHist (semiringEncodeBHist N))) =
          some (SemiringUp.mk A M Z D E H C P N)
      rw [semiring_decode_encode A,
        semiring_decode_encode M,
        semiring_decode_encode Z,
        semiring_decode_encode D,
        semiring_decode_encode E,
        semiring_decode_encode H,
        semiring_decode_encode C,
        semiring_decode_encode P,
        semiring_decode_encode N]

private theorem semiringToEventFlow_injective {x y : SemiringUp} :
    semiringToEventFlow x = semiringToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = semiringFromEventFlow (semiringToEventFlow x) := (semiring_round_trip x).symm
      _ = semiringFromEventFlow (semiringToEventFlow y) := congrArg semiringFromEventFlow hxy
      _ = some y := semiring_round_trip y
  exact Option.some.inj hsome

private theorem semiring_field_faithful :
    ∀ x y : SemiringUp, semiringFields x = semiringFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 M1 Z1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 M2 Z2 D2 E2 H2 C2 P2 N2 =>
          injection hfields with hA tail0
          injection tail0 with hM tail1
          injection tail1 with hZ tail2
          injection tail2 with hD tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hA
          subst hM
          subst hZ
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance semiringBHistCarrier : BHistCarrier SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := semiringToEventFlow
  fromEventFlow := semiringFromEventFlow

instance semiringChapterTasteGate : ChapterTasteGate SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change semiringFromEventFlow (semiringToEventFlow x) = some x
    exact semiring_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (semiringToEventFlow_injective heq)

instance semiringFieldFaithful : FieldFaithful SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := semiringFields
  field_faithful := semiring_field_faithful

instance semiringNontrivial : Nontrivial SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SemiringUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SemiringUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SemiringUp :=
  -- BEDC touchpoint anchor: BHist BMark
  semiringChapterTasteGate

theorem SemiringTasteGate_single_carrier_alignment :
    (∀ h : BHist, semiringDecodeBHist (semiringEncodeBHist h) = h) ∧
      (∀ x : SemiringUp, semiringFromEventFlow (semiringToEventFlow x) = some x) ∧
      (∀ x y : SemiringUp, semiringToEventFlow x = semiringToEventFlow y → x = y) ∧
      semiringEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨semiring_decode_encode,
      semiring_round_trip,
      fun _ _ hxy => semiringToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.SemiringUp.TasteGate
