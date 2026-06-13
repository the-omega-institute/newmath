import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SupportNerveRealizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SupportNerveRealizationUp : Type where
  | mk (S F K A B L H C P N : BHist) : SupportNerveRealizationUp
  deriving DecidableEq

def supportNerveRealizationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: supportNerveRealizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: supportNerveRealizationEncodeBHist h

def supportNerveRealizationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (supportNerveRealizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (supportNerveRealizationDecodeBHist tail)

private theorem SupportNerveRealizationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def supportNerveRealizationFields : SupportNerveRealizationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SupportNerveRealizationUp.mk S F K A B L H C P N => [S, F, K, A, B, L, H, C, P, N]

def supportNerveRealizationToEventFlow : SupportNerveRealizationUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (supportNerveRealizationFields x).map supportNerveRealizationEncodeBHist

private def supportNerveRealizationRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => supportNerveRealizationRawAt index rest

def supportNerveRealizationFromEventFlow
    (flow : EventFlow) : Option SupportNerveRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SupportNerveRealizationUp.mk
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 0 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 1 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 2 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 3 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 4 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 5 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 6 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 7 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 8 flow))
      (supportNerveRealizationDecodeBHist (supportNerveRealizationRawAt 9 flow)))

private theorem SupportNerveRealizationTasteGate_single_carrier_alignment_round_trip :
    forall x : SupportNerveRealizationUp,
      supportNerveRealizationFromEventFlow
        (supportNerveRealizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S F K A B L H C P N =>
      change
        some
          (SupportNerveRealizationUp.mk
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist S))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist F))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist K))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist A))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist B))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist L))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist H))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist C))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist P))
            (supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist N))) =
          some (SupportNerveRealizationUp.mk S F K A B L H C P N)
      rw [SupportNerveRealizationTasteGate_single_carrier_alignment_decode S,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode F,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode K,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode A,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode B,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode L,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode H,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode C,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode P,
        SupportNerveRealizationTasteGate_single_carrier_alignment_decode N]

private theorem supportNerveRealizationToEventFlow_injective
    {x y : SupportNerveRealizationUp} :
    supportNerveRealizationToEventFlow x = supportNerveRealizationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      supportNerveRealizationFromEventFlow (supportNerveRealizationToEventFlow x) =
        supportNerveRealizationFromEventFlow (supportNerveRealizationToEventFlow y) :=
    congrArg supportNerveRealizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SupportNerveRealizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SupportNerveRealizationTasteGate_single_carrier_alignment_round_trip y)))

instance supportNerveRealizationBHistCarrier : BHistCarrier SupportNerveRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := supportNerveRealizationToEventFlow
  fromEventFlow := supportNerveRealizationFromEventFlow

instance supportNerveRealizationChapterTasteGate :
    ChapterTasteGate SupportNerveRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      supportNerveRealizationFromEventFlow (supportNerveRealizationToEventFlow x) = some x
    exact SupportNerveRealizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (supportNerveRealizationToEventFlow_injective heq)

instance supportNerveRealizationFieldFaithful : FieldFaithful SupportNerveRealizationUp where
  fields := supportNerveRealizationFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk S1 F1 K1 A1 B1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 F2 K2 A2 B2 L2 H2 C2 P2 N2 =>
        simp only [supportNerveRealizationFields] at h
        injection h with hS tail1
        injection tail1 with hF tail2
        injection tail2 with hK tail3
        injection tail3 with hA tail4
        injection tail4 with hB tail5
        injection tail5 with hL tail6
        injection tail6 with hH tail7
        injection tail7 with hC tail8
        injection tail8 with hP tail9
        injection tail9 with hN _
        subst hS; subst hF; subst hK; subst hA; subst hB
        subst hL; subst hH; subst hC; subst hP; subst hN
        rfl

def taste_gate : ChapterTasteGate SupportNerveRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  supportNerveRealizationChapterTasteGate

theorem SupportNerveRealizationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      supportNerveRealizationDecodeBHist (supportNerveRealizationEncodeBHist h) = h) ∧
      (forall x : SupportNerveRealizationUp,
        supportNerveRealizationFromEventFlow
          (supportNerveRealizationToEventFlow x) = some x) ∧
      (forall x y : SupportNerveRealizationUp,
        supportNerveRealizationToEventFlow x = supportNerveRealizationToEventFlow y ->
          x = y) ∧
      supportNerveRealizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨SupportNerveRealizationTasteGate_single_carrier_alignment_decode,
      SupportNerveRealizationTasteGate_single_carrier_alignment_round_trip,
      (fun _x _y heq => supportNerveRealizationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SupportNerveRealizationUp
