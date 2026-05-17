import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverSupportLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverSupportLatticeUp : Type where
  | mk (F S C B R H Q P N : BHist) : ObserverSupportLatticeUp
  deriving DecidableEq

def observerSupportLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerSupportLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerSupportLatticeEncodeBHist h

def observerSupportLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerSupportLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerSupportLatticeDecodeBHist tail)

private theorem observerSupportLattice_decode_encode_bhist :
    ∀ h : BHist,
      observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerSupportLatticeFields : ObserverSupportLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverSupportLatticeUp.mk F S C B R H Q P N => [F, S, C, B, R, H, Q, P, N]

def observerSupportLatticeToEventFlow : ObserverSupportLatticeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverSupportLatticeUp.mk F S C B R H Q P N =>
      [observerSupportLatticeEncodeBHist F,
        observerSupportLatticeEncodeBHist S,
        observerSupportLatticeEncodeBHist C,
        observerSupportLatticeEncodeBHist B,
        observerSupportLatticeEncodeBHist R,
        observerSupportLatticeEncodeBHist H,
        observerSupportLatticeEncodeBHist Q,
        observerSupportLatticeEncodeBHist P,
        observerSupportLatticeEncodeBHist N]

def observerSupportLatticeFromEventFlow :
    EventFlow → Option ObserverSupportLatticeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | C :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ObserverSupportLatticeUp.mk
                                              (observerSupportLatticeDecodeBHist F)
                                              (observerSupportLatticeDecodeBHist S)
                                              (observerSupportLatticeDecodeBHist C)
                                              (observerSupportLatticeDecodeBHist B)
                                              (observerSupportLatticeDecodeBHist R)
                                              (observerSupportLatticeDecodeBHist H)
                                              (observerSupportLatticeDecodeBHist Q)
                                              (observerSupportLatticeDecodeBHist P)
                                              (observerSupportLatticeDecodeBHist N))
                                      | _ :: _ => none

private theorem observerSupportLattice_round_trip :
    ∀ x : ObserverSupportLatticeUp,
      observerSupportLatticeFromEventFlow (observerSupportLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S C B R H Q P N =>
      change
        some
          (ObserverSupportLatticeUp.mk
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist F))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist S))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist C))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist B))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist R))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist H))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist Q))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist P))
            (observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist N))) =
          some (ObserverSupportLatticeUp.mk F S C B R H Q P N)
      rw [observerSupportLattice_decode_encode_bhist F,
        observerSupportLattice_decode_encode_bhist S,
        observerSupportLattice_decode_encode_bhist C,
        observerSupportLattice_decode_encode_bhist B,
        observerSupportLattice_decode_encode_bhist R,
        observerSupportLattice_decode_encode_bhist H,
        observerSupportLattice_decode_encode_bhist Q,
        observerSupportLattice_decode_encode_bhist P,
        observerSupportLattice_decode_encode_bhist N]

private theorem observerSupportLatticeToEventFlow_injective
    {x y : ObserverSupportLatticeUp} :
    observerSupportLatticeToEventFlow x = observerSupportLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerSupportLatticeFromEventFlow (observerSupportLatticeToEventFlow x) =
        observerSupportLatticeFromEventFlow (observerSupportLatticeToEventFlow y) :=
    congrArg observerSupportLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerSupportLattice_round_trip x).symm
      (Eq.trans hread (observerSupportLattice_round_trip y)))

private theorem observerSupportLattice_field_faithful :
    ∀ x y : ObserverSupportLatticeUp,
      observerSupportLatticeFields x = observerSupportLatticeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk F₁ S₁ C₁ B₁ R₁ H₁ Q₁ P₁ N₁ =>
      cases y with
      | mk F₂ S₂ C₂ B₂ R₂ H₂ Q₂ P₂ N₂ =>
          cases h
          rfl

instance observerSupportLatticeBHistCarrier : BHistCarrier ObserverSupportLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerSupportLatticeToEventFlow
  fromEventFlow := observerSupportLatticeFromEventFlow

instance observerSupportLatticeChapterTasteGate :
    ChapterTasteGate ObserverSupportLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerSupportLatticeFromEventFlow (observerSupportLatticeToEventFlow x) = some x
    exact observerSupportLattice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerSupportLatticeToEventFlow_injective heq)

instance observerSupportLatticeFieldFaithful : FieldFaithful ObserverSupportLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerSupportLatticeFields
  field_faithful := observerSupportLattice_field_faithful

instance observerSupportLatticeNontrivial : Nontrivial ObserverSupportLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverSupportLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverSupportLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverSupportLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerSupportLatticeChapterTasteGate

theorem ObserverSupportLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        observerSupportLatticeDecodeBHist (observerSupportLatticeEncodeBHist h) = h) ∧
      (∀ x : ObserverSupportLatticeUp,
        observerSupportLatticeFromEventFlow (observerSupportLatticeToEventFlow x) = some x) ∧
      (∀ x y : ObserverSupportLatticeUp,
        observerSupportLatticeToEventFlow x = observerSupportLatticeToEventFlow y → x = y) ∧
      Nonempty
        (@ChapterTasteGate ObserverSupportLatticeUp observerSupportLatticeBHistCarrier) ∧
      (∀ x y : ObserverSupportLatticeUp,
        observerSupportLatticeFields x = observerSupportLatticeFields y → x = y) ∧
      observerSupportLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨observerSupportLattice_decode_encode_bhist, observerSupportLattice_round_trip,
    fun _ _ heq => observerSupportLatticeToEventFlow_injective heq,
    ⟨observerSupportLatticeChapterTasteGate⟩, observerSupportLattice_field_faithful, rfl⟩

end BEDC.Derived.ObserverSupportLatticeUp
