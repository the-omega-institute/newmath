import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EberleinSmulianUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EberleinSmulianUp : Type where
  | mk (F H K M Q W U L E T C P N : BHist) : EberleinSmulianUp
  deriving DecidableEq

def eberleinSmulianEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eberleinSmulianEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eberleinSmulianEncodeBHist h

def eberleinSmulianDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eberleinSmulianDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eberleinSmulianDecodeBHist tail)

private theorem EberleinSmulianTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eberleinSmulianFields : EberleinSmulianUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EberleinSmulianUp.mk F H K M Q W U L E T C P N =>
      [F, H, K, M, Q, W, U, L, E, T, C, P, N]

def eberleinSmulianToEventFlow : EberleinSmulianUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eberleinSmulianFields x).map eberleinSmulianEncodeBHist

private def eberleinSmulianEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eberleinSmulianEventAtDefault index rest

def eberleinSmulianFromEventFlow (ef : EventFlow) : Option EberleinSmulianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EberleinSmulianUp.mk
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 0 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 1 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 2 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 3 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 4 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 5 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 6 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 7 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 8 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 9 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 10 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 11 ef))
      (eberleinSmulianDecodeBHist (eberleinSmulianEventAtDefault 12 ef)))

private theorem EberleinSmulianTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EberleinSmulianUp,
      eberleinSmulianFromEventFlow (eberleinSmulianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F H K M Q W U L E T C P N =>
      change
        some
          (EberleinSmulianUp.mk
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist F))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist H))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist K))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist M))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist Q))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist W))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist U))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist L))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist E))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist T))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist C))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist P))
            (eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist N))) =
          some (EberleinSmulianUp.mk F H K M Q W U L E T C P N)
      rw [EberleinSmulianTasteGate_single_carrier_alignment_decode F,
        EberleinSmulianTasteGate_single_carrier_alignment_decode H,
        EberleinSmulianTasteGate_single_carrier_alignment_decode K,
        EberleinSmulianTasteGate_single_carrier_alignment_decode M,
        EberleinSmulianTasteGate_single_carrier_alignment_decode Q,
        EberleinSmulianTasteGate_single_carrier_alignment_decode W,
        EberleinSmulianTasteGate_single_carrier_alignment_decode U,
        EberleinSmulianTasteGate_single_carrier_alignment_decode L,
        EberleinSmulianTasteGate_single_carrier_alignment_decode E,
        EberleinSmulianTasteGate_single_carrier_alignment_decode T,
        EberleinSmulianTasteGate_single_carrier_alignment_decode C,
        EberleinSmulianTasteGate_single_carrier_alignment_decode P,
        EberleinSmulianTasteGate_single_carrier_alignment_decode N]

private theorem EberleinSmulianTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EberleinSmulianUp} :
    eberleinSmulianToEventFlow x = eberleinSmulianToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eberleinSmulianFromEventFlow (eberleinSmulianToEventFlow x) =
        eberleinSmulianFromEventFlow (eberleinSmulianToEventFlow y) :=
    congrArg eberleinSmulianFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EberleinSmulianTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EberleinSmulianTasteGate_single_carrier_alignment_round_trip y)))

private theorem EberleinSmulianTasteGate_single_carrier_alignment_fields :
    ∀ x y : EberleinSmulianUp, eberleinSmulianFields x = eberleinSmulianFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 H1 K1 M1 Q1 W1 U1 L1 E1 T1 C1 P1 N1 =>
      cases y with
      | mk F2 H2 K2 M2 Q2 W2 U2 L2 E2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance eberleinSmulianBHistCarrier : BHistCarrier EberleinSmulianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eberleinSmulianToEventFlow
  fromEventFlow := eberleinSmulianFromEventFlow

instance eberleinSmulianChapterTasteGate : ChapterTasteGate EberleinSmulianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eberleinSmulianFromEventFlow (eberleinSmulianToEventFlow x) = some x
    exact EberleinSmulianTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EberleinSmulianTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance eberleinSmulianFieldFaithful : FieldFaithful EberleinSmulianUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eberleinSmulianFields
  field_faithful := EberleinSmulianTasteGate_single_carrier_alignment_fields

instance eberleinSmulianNontrivial : Nontrivial EberleinSmulianUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EberleinSmulianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      EberleinSmulianUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EberleinSmulianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eberleinSmulianChapterTasteGate

theorem EberleinSmulianTasteGate_single_carrier_alignment :
    (∀ h : BHist, eberleinSmulianDecodeBHist (eberleinSmulianEncodeBHist h) = h) ∧
      (∀ x : EberleinSmulianUp,
        eberleinSmulianFromEventFlow (eberleinSmulianToEventFlow x) = some x) ∧
        (∀ x y : EberleinSmulianUp,
          eberleinSmulianToEventFlow x = eberleinSmulianToEventFlow y → x = y) ∧
          eberleinSmulianEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨EberleinSmulianTasteGate_single_carrier_alignment_decode,
      EberleinSmulianTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => EberleinSmulianTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EberleinSmulianUp
