import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDischargeObstructionLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDischargeObstructionLatticeUp : Type where
  | mk :
      (closedNormal decidableChecker confluenceStatus obstruction obligation transport route
        provenance name : BHist) →
      MetaCICDischargeObstructionLatticeUp
  deriving DecidableEq

def metaCICDischargeObstructionLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICDischargeObstructionLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICDischargeObstructionLatticeEncodeBHist h

def metaCICDischargeObstructionLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICDischargeObstructionLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICDischargeObstructionLatticeDecodeBHist tail)

private theorem metaCICDischargeObstructionLattice_decode_encode_bhist :
    ∀ h : BHist,
      metaCICDischargeObstructionLatticeDecodeBHist
        (metaCICDischargeObstructionLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICDischargeObstructionLatticeToEventFlow :
    MetaCICDischargeObstructionLatticeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDischargeObstructionLatticeUp.mk closedNormal decidableChecker confluenceStatus
      obstruction obligation transport route provenance name =>
      [[BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist closedNormal,
        [BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist decidableChecker,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist confluenceStatus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist obligation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICDischargeObstructionLatticeEncodeBHist name]

private def metaCICDischargeObstructionLatticeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => metaCICDischargeObstructionLatticeRawAt n rest

private def metaCICDischargeObstructionLatticeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => metaCICDischargeObstructionLatticeLengthEq n rest

def metaCICDischargeObstructionLatticeFromEventFlow :
    EventFlow → Option MetaCICDischargeObstructionLatticeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match metaCICDischargeObstructionLatticeLengthEq 18 flow with
      | true =>
          some
            (MetaCICDischargeObstructionLatticeUp.mk
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 1 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 3 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 5 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 7 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 9 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 11 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 13 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 15 flow))
              (metaCICDischargeObstructionLatticeDecodeBHist
                (metaCICDischargeObstructionLatticeRawAt 17 flow)))
      | false => none

private theorem metaCICDischargeObstructionLattice_round_trip :
    ∀ x : MetaCICDischargeObstructionLatticeUp,
      metaCICDischargeObstructionLatticeFromEventFlow
        (metaCICDischargeObstructionLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk closedNormal decidableChecker confluenceStatus obstruction obligation transport route
      provenance name =>
      change
        some
          (MetaCICDischargeObstructionLatticeUp.mk
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist closedNormal))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist decidableChecker))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist confluenceStatus))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist obstruction))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist obligation))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist transport))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist route))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist provenance))
            (metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist name))) =
          some
            (MetaCICDischargeObstructionLatticeUp.mk closedNormal decidableChecker
              confluenceStatus obstruction obligation transport route provenance name)
      rw [metaCICDischargeObstructionLattice_decode_encode_bhist closedNormal,
        metaCICDischargeObstructionLattice_decode_encode_bhist decidableChecker,
        metaCICDischargeObstructionLattice_decode_encode_bhist confluenceStatus,
        metaCICDischargeObstructionLattice_decode_encode_bhist obstruction,
        metaCICDischargeObstructionLattice_decode_encode_bhist obligation,
        metaCICDischargeObstructionLattice_decode_encode_bhist transport,
        metaCICDischargeObstructionLattice_decode_encode_bhist route,
        metaCICDischargeObstructionLattice_decode_encode_bhist provenance,
        metaCICDischargeObstructionLattice_decode_encode_bhist name]

private theorem metaCICDischargeObstructionLatticeToEventFlow_injective
    {x y : MetaCICDischargeObstructionLatticeUp} :
    metaCICDischargeObstructionLatticeToEventFlow x =
      metaCICDischargeObstructionLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICDischargeObstructionLatticeFromEventFlow
          (metaCICDischargeObstructionLatticeToEventFlow x) =
        metaCICDischargeObstructionLatticeFromEventFlow
          (metaCICDischargeObstructionLatticeToEventFlow y) :=
    congrArg metaCICDischargeObstructionLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICDischargeObstructionLattice_round_trip x).symm
      (Eq.trans hread (metaCICDischargeObstructionLattice_round_trip y)))

instance metaCICDischargeObstructionLatticeBHistCarrier :
    BHistCarrier MetaCICDischargeObstructionLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICDischargeObstructionLatticeToEventFlow
  fromEventFlow := metaCICDischargeObstructionLatticeFromEventFlow

instance metaCICDischargeObstructionLatticeChapterTasteGate :
    ChapterTasteGate MetaCICDischargeObstructionLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICDischargeObstructionLatticeFromEventFlow
        (metaCICDischargeObstructionLatticeToEventFlow x) = some x
    exact metaCICDischargeObstructionLattice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICDischargeObstructionLatticeToEventFlow_injective heq)

instance metaCICDischargeObstructionLatticeFieldFaithful :
    FieldFaithful MetaCICDischargeObstructionLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICDischargeObstructionLatticeUp.mk closedNormal decidableChecker
        confluenceStatus obstruction obligation transport route provenance name =>
        [closedNormal, decidableChecker, confluenceStatus, obstruction, obligation, transport,
          route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk closedNormal1 decidableChecker1 confluenceStatus1 obstruction1 obligation1 transport1
        route1 provenance1 name1 =>
        cases y with
        | mk closedNormal2 decidableChecker2 confluenceStatus2 obstruction2 obligation2
            transport2 route2 provenance2 name2 =>
            cases h
            rfl

instance metaCICDischargeObstructionLatticeNontrivial :
    Nontrivial MetaCICDischargeObstructionLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICDischargeObstructionLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICDischargeObstructionLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICDischargeObstructionLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICDischargeObstructionLatticeChapterTasteGate

theorem MetaCICDischargeObstructionLatticeTasteGate_single_carrier_alignment :
    ChapterTasteGate MetaCICDischargeObstructionLatticeUp ∧
      Nonempty (Nontrivial MetaCICDischargeObstructionLatticeUp) ∧
        Nonempty (FieldFaithful MetaCICDischargeObstructionLatticeUp) ∧
          (∀ h : BHist,
            metaCICDischargeObstructionLatticeDecodeBHist
              (metaCICDischargeObstructionLatticeEncodeBHist h) = h) ∧
            (∀ x y : MetaCICDischargeObstructionLatticeUp,
              metaCICDischargeObstructionLatticeToEventFlow x =
                metaCICDischargeObstructionLatticeToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨metaCICDischargeObstructionLatticeChapterTasteGate,
      ⟨metaCICDischargeObstructionLatticeNontrivial⟩,
      ⟨metaCICDischargeObstructionLatticeFieldFaithful⟩,
      metaCICDischargeObstructionLattice_decode_encode_bhist,
      by
        intro x y heq
        exact metaCICDischargeObstructionLatticeToEventFlow_injective heq⟩

end BEDC.Derived.MetaCICDischargeObstructionLatticeUp
