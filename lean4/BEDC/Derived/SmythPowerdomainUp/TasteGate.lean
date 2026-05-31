import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SmythPowerdomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SmythPowerdomainUp : Type where
  | mk (F I W S C H R G Q N : BHist) : SmythPowerdomainUp
  deriving DecidableEq

def smythPowerdomainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: smythPowerdomainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: smythPowerdomainEncodeBHist h

def smythPowerdomainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (smythPowerdomainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (smythPowerdomainDecodeBHist tail)

private theorem SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def smythPowerdomainFields : SmythPowerdomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SmythPowerdomainUp.mk F I W S C H R G Q N => [F, I, W, S, C, H, R, G, Q, N]

def smythPowerdomainToEventFlow : SmythPowerdomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (smythPowerdomainFields x).map smythPowerdomainEncodeBHist

def smythPowerdomainFromEventFlow : EventFlow → Option SmythPowerdomainUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | G :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Q :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (SmythPowerdomainUp.mk
                                                  (smythPowerdomainDecodeBHist F)
                                                  (smythPowerdomainDecodeBHist I)
                                                  (smythPowerdomainDecodeBHist W)
                                                  (smythPowerdomainDecodeBHist S)
                                                  (smythPowerdomainDecodeBHist C)
                                                  (smythPowerdomainDecodeBHist H)
                                                  (smythPowerdomainDecodeBHist R)
                                                  (smythPowerdomainDecodeBHist G)
                                                  (smythPowerdomainDecodeBHist Q)
                                                  (smythPowerdomainDecodeBHist N))
                                          | _ :: _ => none

private theorem SmythPowerdomainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SmythPowerdomainUp,
      smythPowerdomainFromEventFlow (smythPowerdomainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I W S C H R G Q N =>
      change
        some
            (SmythPowerdomainUp.mk
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist F))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist I))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist W))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist S))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist C))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist H))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist R))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist G))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist Q))
              (smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist N))) =
          some (SmythPowerdomainUp.mk F I W S C H R G Q N)
      rw [SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode F,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode I,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode W,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode S,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode C,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode H,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode R,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode G,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode Q,
        SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode N]

private theorem SmythPowerdomainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SmythPowerdomainUp} :
    smythPowerdomainToEventFlow x = smythPowerdomainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      smythPowerdomainFromEventFlow (smythPowerdomainToEventFlow x) =
        smythPowerdomainFromEventFlow (smythPowerdomainToEventFlow y) :=
    congrArg smythPowerdomainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SmythPowerdomainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SmythPowerdomainTasteGate_single_carrier_alignment_round_trip y)))

private theorem SmythPowerdomainTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : SmythPowerdomainUp, smythPowerdomainFields x = smythPowerdomainFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ I₁ W₁ S₁ C₁ H₁ R₁ G₁ Q₁ N₁ =>
      cases y with
      | mk F₂ I₂ W₂ S₂ C₂ H₂ R₂ G₂ Q₂ N₂ =>
          cases hfields
          rfl

instance smythPowerdomainBHistCarrier : BHistCarrier SmythPowerdomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := smythPowerdomainToEventFlow
  fromEventFlow := smythPowerdomainFromEventFlow

instance smythPowerdomainChapterTasteGate : ChapterTasteGate SmythPowerdomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change smythPowerdomainFromEventFlow (smythPowerdomainToEventFlow x) = some x
    exact SmythPowerdomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SmythPowerdomainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance smythPowerdomainFieldFaithful : FieldFaithful SmythPowerdomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := smythPowerdomainFields
  field_faithful := SmythPowerdomainTasteGate_single_carrier_alignment_field_faithful

instance smythPowerdomainNontrivial : Nontrivial SmythPowerdomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SmythPowerdomainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SmythPowerdomainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SmythPowerdomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  smythPowerdomainChapterTasteGate

theorem SmythPowerdomainTasteGate_single_carrier_alignment :
    (forall h : BHist, smythPowerdomainDecodeBHist (smythPowerdomainEncodeBHist h) = h) ∧
      (forall x : SmythPowerdomainUp,
        smythPowerdomainFromEventFlow (smythPowerdomainToEventFlow x) = some x) ∧
        (forall x y : SmythPowerdomainUp,
          smythPowerdomainToEventFlow x = smythPowerdomainToEventFlow y -> x = y) ∧
          smythPowerdomainEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (forall x y : SmythPowerdomainUp,
              smythPowerdomainFields x = smythPowerdomainFields y -> x = y) ∧
              (exists x y : SmythPowerdomainUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SmythPowerdomainTasteGate_single_carrier_alignment_decode_encode,
      SmythPowerdomainTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SmythPowerdomainTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      SmythPowerdomainTasteGate_single_carrier_alignment_field_faithful,
      ⟨SmythPowerdomainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        SmythPowerdomainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.SmythPowerdomainUp
