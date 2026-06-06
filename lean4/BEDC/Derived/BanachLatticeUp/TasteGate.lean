import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachLatticeUp : Type where
  | mk (R A N P M H C S : BHist) : BanachLatticeUp
  deriving DecidableEq

def banachLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachLatticeEncodeBHist h

def banachLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachLatticeDecodeBHist tail)

private theorem BanachLatticeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, banachLatticeDecodeBHist (banachLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachLatticeFields : BanachLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachLatticeUp.mk R A N P M H C S => [R, A, N, P, M, H, C, S]

def banachLatticeToEventFlow : BanachLatticeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (banachLatticeFields x).map banachLatticeEncodeBHist

private def banachLatticeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachLatticeEventAtDefault index rest

def banachLatticeFromEventFlow (ef : EventFlow) : Option BanachLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachLatticeUp.mk
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 0 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 1 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 2 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 3 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 4 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 5 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 6 ef))
      (banachLatticeDecodeBHist (banachLatticeEventAtDefault 7 ef)))

private theorem BanachLatticeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachLatticeUp,
      banachLatticeFromEventFlow (banachLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R A N P M H C S =>
      change
        some
          (BanachLatticeUp.mk
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist R))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist A))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist N))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist P))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist M))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist H))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist C))
            (banachLatticeDecodeBHist (banachLatticeEncodeBHist S))) =
          some (BanachLatticeUp.mk R A N P M H C S)
      rw [BanachLatticeTasteGate_single_carrier_alignment_decode R,
        BanachLatticeTasteGate_single_carrier_alignment_decode A,
        BanachLatticeTasteGate_single_carrier_alignment_decode N,
        BanachLatticeTasteGate_single_carrier_alignment_decode P,
        BanachLatticeTasteGate_single_carrier_alignment_decode M,
        BanachLatticeTasteGate_single_carrier_alignment_decode H,
        BanachLatticeTasteGate_single_carrier_alignment_decode C,
        BanachLatticeTasteGate_single_carrier_alignment_decode S]

private theorem BanachLatticeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachLatticeUp} :
    banachLatticeToEventFlow x = banachLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachLatticeFromEventFlow (banachLatticeToEventFlow x) =
        banachLatticeFromEventFlow (banachLatticeToEventFlow y) :=
    congrArg banachLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BanachLatticeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachLatticeTasteGate_single_carrier_alignment_round_trip y)))

private theorem BanachLatticeTasteGate_single_carrier_alignment_fields :
    ∀ x y : BanachLatticeUp, banachLatticeFields x = banachLatticeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 A1 N1 P1 M1 H1 C1 S1 =>
      cases y with
      | mk R2 A2 N2 P2 M2 H2 C2 S2 =>
          cases hfields
          rfl

instance banachLatticeBHistCarrier : BHistCarrier BanachLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachLatticeToEventFlow
  fromEventFlow := banachLatticeFromEventFlow

instance banachLatticeChapterTasteGate : ChapterTasteGate BanachLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachLatticeFromEventFlow (banachLatticeToEventFlow x) = some x
    exact BanachLatticeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachLatticeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance banachLatticeFieldFaithful : FieldFaithful BanachLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachLatticeFields
  field_faithful := BanachLatticeTasteGate_single_carrier_alignment_fields

instance banachLatticeNontrivial : Nontrivial BanachLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BanachLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachLatticeChapterTasteGate

theorem BanachLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist, banachLatticeDecodeBHist (banachLatticeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BanachLatticeUp) ∧
        Nonempty (ChapterTasteGate BanachLatticeUp) ∧
          banachLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BanachLatticeTasteGate_single_carrier_alignment_decode,
      ⟨banachLatticeBHistCarrier⟩, ⟨banachLatticeChapterTasteGate⟩, rfl⟩

end BEDC.Derived.BanachLatticeUp
