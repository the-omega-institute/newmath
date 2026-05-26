import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardIterationUp : Type where
  | mk (X T x0 I r M R E H C Q N : BHist) : PicardIterationUp
  deriving DecidableEq

def picardIterationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardIterationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardIterationEncodeBHist h

def picardIterationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardIterationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardIterationDecodeBHist tail)

private theorem PicardIterationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, picardIterationDecodeBHist (picardIterationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardIterationFields : PicardIterationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardIterationUp.mk X T x0 I r M R E H C Q N =>
      [X, T, x0, I, r, M, R, E, H, C, Q, N]

def picardIterationToEventFlow : PicardIterationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (picardIterationFields x).map picardIterationEncodeBHist

private def picardIterationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => picardIterationEventAtDefault index rest

def picardIterationFromEventFlow (ef : EventFlow) : Option PicardIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PicardIterationUp.mk
      (picardIterationDecodeBHist (picardIterationEventAtDefault 0 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 1 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 2 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 3 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 4 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 5 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 6 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 7 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 8 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 9 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 10 ef))
      (picardIterationDecodeBHist (picardIterationEventAtDefault 11 ef)))

private theorem PicardIterationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PicardIterationUp,
      picardIterationFromEventFlow (picardIterationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T x0 I r M R E H C Q N =>
      change
        some
          (PicardIterationUp.mk
            (picardIterationDecodeBHist (picardIterationEncodeBHist X))
            (picardIterationDecodeBHist (picardIterationEncodeBHist T))
            (picardIterationDecodeBHist (picardIterationEncodeBHist x0))
            (picardIterationDecodeBHist (picardIterationEncodeBHist I))
            (picardIterationDecodeBHist (picardIterationEncodeBHist r))
            (picardIterationDecodeBHist (picardIterationEncodeBHist M))
            (picardIterationDecodeBHist (picardIterationEncodeBHist R))
            (picardIterationDecodeBHist (picardIterationEncodeBHist E))
            (picardIterationDecodeBHist (picardIterationEncodeBHist H))
            (picardIterationDecodeBHist (picardIterationEncodeBHist C))
            (picardIterationDecodeBHist (picardIterationEncodeBHist Q))
            (picardIterationDecodeBHist (picardIterationEncodeBHist N))) =
          some (PicardIterationUp.mk X T x0 I r M R E H C Q N)
      rw [PicardIterationTasteGate_single_carrier_alignment_decode X,
        PicardIterationTasteGate_single_carrier_alignment_decode T,
        PicardIterationTasteGate_single_carrier_alignment_decode x0,
        PicardIterationTasteGate_single_carrier_alignment_decode I,
        PicardIterationTasteGate_single_carrier_alignment_decode r,
        PicardIterationTasteGate_single_carrier_alignment_decode M,
        PicardIterationTasteGate_single_carrier_alignment_decode R,
        PicardIterationTasteGate_single_carrier_alignment_decode E,
        PicardIterationTasteGate_single_carrier_alignment_decode H,
        PicardIterationTasteGate_single_carrier_alignment_decode C,
        PicardIterationTasteGate_single_carrier_alignment_decode Q,
        PicardIterationTasteGate_single_carrier_alignment_decode N]

private theorem PicardIterationTasteGate_single_carrier_alignment_injective
    {x y : PicardIterationUp} :
    picardIterationToEventFlow x = picardIterationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardIterationFromEventFlow (picardIterationToEventFlow x) =
        picardIterationFromEventFlow (picardIterationToEventFlow y) :=
    congrArg picardIterationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PicardIterationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PicardIterationTasteGate_single_carrier_alignment_round_trip y)))

private theorem PicardIterationTasteGate_single_carrier_alignment_fields :
    ∀ x y : PicardIterationUp, picardIterationFields x = picardIterationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 T1 x01 I1 r1 M1 R1 E1 H1 C1 Q1 N1 =>
      cases y with
      | mk X2 T2 x02 I2 r2 M2 R2 E2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance picardIterationBHistCarrier : BHistCarrier PicardIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardIterationToEventFlow
  fromEventFlow := picardIterationFromEventFlow

instance picardIterationChapterTasteGate : ChapterTasteGate PicardIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change picardIterationFromEventFlow (picardIterationToEventFlow x) = some x
    exact PicardIterationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PicardIterationTasteGate_single_carrier_alignment_injective heq)

instance picardIterationFieldFaithful : FieldFaithful PicardIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := picardIterationFields
  field_faithful := PicardIterationTasteGate_single_carrier_alignment_fields

instance picardIterationNontrivial : Nontrivial PicardIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PicardIterationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PicardIterationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PicardIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  picardIterationChapterTasteGate

theorem PicardIterationTasteGate_single_carrier_alignment :
    (∀ h : BHist, picardIterationDecodeBHist (picardIterationEncodeBHist h) = h) ∧
      (∀ x : PicardIterationUp,
        picardIterationFromEventFlow (picardIterationToEventFlow x) = some x) ∧
        (∀ x y : PicardIterationUp,
          picardIterationToEventFlow x = picardIterationToEventFlow y → x = y) ∧
          picardIterationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨PicardIterationTasteGate_single_carrier_alignment_decode,
      PicardIterationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PicardIterationTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.PicardIterationUp
