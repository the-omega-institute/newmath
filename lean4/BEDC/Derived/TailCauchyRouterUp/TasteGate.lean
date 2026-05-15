import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailCauchyRouterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailCauchyRouterUp : Type where
  | mk (S M W R L E H C P N : BHist) : TailCauchyRouterUp
  deriving DecidableEq

def tailCauchyRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailCauchyRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailCauchyRouterEncodeBHist h

def tailCauchyRouterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailCauchyRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailCauchyRouterDecodeBHist tail)

private theorem TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      tailCauchyRouterDecodeBHist
        (tailCauchyRouterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tailCauchyRouterFields :
    TailCauchyRouterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TailCauchyRouterUp.mk S M W R L E H C P N => [S, M, W, R, L, E, H, C, P, N]

def tailCauchyRouterToEventFlow :
    TailCauchyRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tailCauchyRouterFields x).map tailCauchyRouterEncodeBHist

def tailCauchyRouterFromEventFlow :
    EventFlow → Option TailCauchyRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (TailCauchyRouterUp.mk
                                                  (tailCauchyRouterDecodeBHist S)
                                                  (tailCauchyRouterDecodeBHist M)
                                                  (tailCauchyRouterDecodeBHist W)
                                                  (tailCauchyRouterDecodeBHist R)
                                                  (tailCauchyRouterDecodeBHist L)
                                                  (tailCauchyRouterDecodeBHist E)
                                                  (tailCauchyRouterDecodeBHist H)
                                                  (tailCauchyRouterDecodeBHist C)
                                                  (tailCauchyRouterDecodeBHist P)
                                                  (tailCauchyRouterDecodeBHist N))
                                          | _ :: _ => none

private theorem TailCauchyRouterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TailCauchyRouterUp,
      tailCauchyRouterFromEventFlow
        (tailCauchyRouterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W R L E H C P N =>
      change
        some
          (TailCauchyRouterUp.mk
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist S))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist M))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist W))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist R))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist L))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist E))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist H))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist C))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist P))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist N))) =
          some (TailCauchyRouterUp.mk S M W R L E H C P N)
      rw [TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode S,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode M,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode W,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode R,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode L,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode E,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode H,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode C,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode P,
        TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode N]

private theorem TailCauchyRouterTasteGate_single_carrier_alignment_injective
    {x y : TailCauchyRouterUp} :
    tailCauchyRouterToEventFlow x =
      tailCauchyRouterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tailCauchyRouterFromEventFlow
          (tailCauchyRouterToEventFlow x) =
        tailCauchyRouterFromEventFlow
          (tailCauchyRouterToEventFlow y) :=
    congrArg tailCauchyRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TailCauchyRouterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TailCauchyRouterTasteGate_single_carrier_alignment_round_trip y)))

private theorem tailCauchyRouter_field_faithful :
    ∀ x y : TailCauchyRouterUp,
      tailCauchyRouterFields x = tailCauchyRouterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ W₁ R₁ L₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ W₂ R₂ L₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance tailCauchyRouterBHistCarrier :
    BHistCarrier TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailCauchyRouterToEventFlow
  fromEventFlow := tailCauchyRouterFromEventFlow

instance tailCauchyRouterChapterTasteGate :
    ChapterTasteGate TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      tailCauchyRouterFromEventFlow
        (tailCauchyRouterToEventFlow x) = some x
    exact TailCauchyRouterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TailCauchyRouterTasteGate_single_carrier_alignment_injective heq)

instance tailCauchyRouterFieldFaithful :
    FieldFaithful TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tailCauchyRouterFields
  field_faithful := tailCauchyRouter_field_faithful

instance tailCauchyRouterNontrivial :
    Nontrivial TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TailCauchyRouterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TailCauchyRouterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TailCauchyRouterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tailCauchyRouterChapterTasteGate

theorem TailCauchyRouterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate TailCauchyRouterUp) ∧
      Nonempty (FieldFaithful TailCauchyRouterUp) ∧
        Nonempty (Nontrivial TailCauchyRouterUp) ∧
          (∀ h : BHist,
            tailCauchyRouterDecodeBHist
              (tailCauchyRouterEncodeBHist h) = h) ∧
            (∀ x : TailCauchyRouterUp,
              tailCauchyRouterFromEventFlow
                (tailCauchyRouterToEventFlow x) = some x) ∧
              (∀ x y : TailCauchyRouterUp,
                tailCauchyRouterToEventFlow x =
                    tailCauchyRouterToEventFlow y →
                  x = y) ∧
                tailCauchyRouterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨tailCauchyRouterChapterTasteGate⟩,
      ⟨tailCauchyRouterFieldFaithful⟩,
      ⟨tailCauchyRouterNontrivial⟩,
      TailCauchyRouterTasteGate_single_carrier_alignment_decode_encode,
      TailCauchyRouterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => TailCauchyRouterTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.TailCauchyRouterUp.TasteGate
