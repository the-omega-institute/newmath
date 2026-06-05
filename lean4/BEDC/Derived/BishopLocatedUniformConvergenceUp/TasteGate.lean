import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedUniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedUniformConvergenceUp : Type where
  | mk (X F L M W R E H C P N : BHist) : BishopLocatedUniformConvergenceUp
  deriving DecidableEq

def bishopLocatedUniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedUniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedUniformConvergenceEncodeBHist h

def bishopLocatedUniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedUniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedUniformConvergenceDecodeBHist tail)

private theorem BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedUniformConvergenceFields :
    BishopLocatedUniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedUniformConvergenceUp.mk X F L M W R E H C P N =>
      [X, F, L, M, W, R, E, H, C, P, N]

def bishopLocatedUniformConvergenceToEventFlow :
    BishopLocatedUniformConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopLocatedUniformConvergenceFields x).map
      bishopLocatedUniformConvergenceEncodeBHist

private def bishopLocatedUniformConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedUniformConvergenceEventAt index rest

def bishopLocatedUniformConvergenceFromEventFlow
    (ef : EventFlow) : Option BishopLocatedUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedUniformConvergenceUp.mk
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 0 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 1 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 2 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 3 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 4 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 5 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 6 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 7 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 8 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 9 ef))
      (bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEventAt 10 ef)))

private theorem BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedUniformConvergenceUp,
      bishopLocatedUniformConvergenceFromEventFlow
        (bishopLocatedUniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X F L M W R E H C P N =>
      change
        some
          (BishopLocatedUniformConvergenceUp.mk
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist X))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist F))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist L))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist M))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist W))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist R))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist E))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist H))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist C))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist P))
            (bishopLocatedUniformConvergenceDecodeBHist
              (bishopLocatedUniformConvergenceEncodeBHist N))) =
          some (BishopLocatedUniformConvergenceUp.mk X F L M W R E H C P N)
      rw [BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode X,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode F,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode L,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode M,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode W,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode R,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode E,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode H,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode C,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode P,
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedUniformConvergenceUp} :
    bishopLocatedUniformConvergenceToEventFlow x =
        bishopLocatedUniformConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedUniformConvergenceFromEventFlow
          (bishopLocatedUniformConvergenceToEventFlow x) =
        bishopLocatedUniformConvergenceFromEventFlow
          (bishopLocatedUniformConvergenceToEventFlow y) :=
    congrArg bishopLocatedUniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopLocatedUniformConvergenceUp,
      bishopLocatedUniformConvergenceFields x =
          bishopLocatedUniformConvergenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 L1 M1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 L2 M2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedUniformConvergenceBHistCarrier :
    BHistCarrier BishopLocatedUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedUniformConvergenceToEventFlow
  fromEventFlow := bishopLocatedUniformConvergenceFromEventFlow

instance bishopLocatedUniformConvergenceChapterTasteGate :
    ChapterTasteGate BishopLocatedUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedUniformConvergenceFromEventFlow
        (bishopLocatedUniformConvergenceToEventFlow x) = some x
    exact BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_injective heq)

instance bishopLocatedUniformConvergenceFieldFaithful :
    FieldFaithful BishopLocatedUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedUniformConvergenceFields
  field_faithful :=
    BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_fields

instance bishopLocatedUniformConvergenceNontrivial :
    Nontrivial BishopLocatedUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedUniformConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BishopLocatedUniformConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedUniformConvergenceChapterTasteGate

theorem BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedUniformConvergenceDecodeBHist
        (bishopLocatedUniformConvergenceEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedUniformConvergenceUp,
        bishopLocatedUniformConvergenceFromEventFlow
          (bishopLocatedUniformConvergenceToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedUniformConvergenceUp,
          bishopLocatedUniformConvergenceToEventFlow x =
              bishopLocatedUniformConvergenceToEventFlow y →
            x = y) ∧
          bishopLocatedUniformConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_decode,
      BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopLocatedUniformConvergenceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BishopLocatedUniformConvergenceUp
