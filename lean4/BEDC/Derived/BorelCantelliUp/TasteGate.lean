import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorelCantelliUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BorelCantelliUp : Type where
  | mk (Omega E W S T U L H C P N : BHist) : BorelCantelliUp
  deriving DecidableEq

def borelCantelliEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: borelCantelliEncodeBHist h
  | BHist.e1 h => BMark.b1 :: borelCantelliEncodeBHist h

def borelCantelliDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (borelCantelliDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (borelCantelliDecodeBHist tail)

private theorem BorelCantelliTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, borelCantelliDecodeBHist (borelCantelliEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def borelCantelliFields : BorelCantelliUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorelCantelliUp.mk Omega E W S T U L H C P N => [Omega, E, W, S, T, U, L, H, C, P, N]

def borelCantelliToEventFlow : BorelCantelliUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (borelCantelliFields x).map borelCantelliEncodeBHist

def borelCantelliFromEventFlow : EventFlow -> Option BorelCantelliUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Omega :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | U :: rest5 =>
                          match rest5 with
                          | [] => none
                          | L :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (BorelCantelliUp.mk
                                                      (borelCantelliDecodeBHist Omega)
                                                      (borelCantelliDecodeBHist E)
                                                      (borelCantelliDecodeBHist W)
                                                      (borelCantelliDecodeBHist S)
                                                      (borelCantelliDecodeBHist T)
                                                      (borelCantelliDecodeBHist U)
                                                      (borelCantelliDecodeBHist L)
                                                      (borelCantelliDecodeBHist H)
                                                      (borelCantelliDecodeBHist C)
                                                      (borelCantelliDecodeBHist P)
                                                      (borelCantelliDecodeBHist N))
                                              | _ :: _ => none

private theorem BorelCantelliTasteGate_single_carrier_alignment_round_trip :
    forall x : BorelCantelliUp,
      borelCantelliFromEventFlow (borelCantelliToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Omega E W S T U L H C P N =>
      change
        some
          (BorelCantelliUp.mk
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist Omega))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist E))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist W))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist S))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist T))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist U))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist L))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist H))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist C))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist P))
            (borelCantelliDecodeBHist (borelCantelliEncodeBHist N))) =
          some (BorelCantelliUp.mk Omega E W S T U L H C P N)
      rw [BorelCantelliTasteGate_single_carrier_alignment_decode_encode Omega,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode E,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode W,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode S,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode T,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode U,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode L,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode H,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode C,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode P,
        BorelCantelliTasteGate_single_carrier_alignment_decode_encode N]

private theorem BorelCantelliTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BorelCantelliUp} :
    borelCantelliToEventFlow x = borelCantelliToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      borelCantelliFromEventFlow (borelCantelliToEventFlow x) =
        borelCantelliFromEventFlow (borelCantelliToEventFlow y) :=
    congrArg borelCantelliFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BorelCantelliTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BorelCantelliTasteGate_single_carrier_alignment_round_trip y)))

private theorem BorelCantelliTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : BorelCantelliUp, borelCantelliFields x = borelCantelliFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Omega1 E1 W1 S1 T1 U1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk Omega2 E2 W2 S2 T2 U2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance borelCantelliBHistCarrier : BHistCarrier BorelCantelliUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := borelCantelliToEventFlow
  fromEventFlow := borelCantelliFromEventFlow

instance borelCantelliChapterTasteGate : ChapterTasteGate BorelCantelliUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change borelCantelliFromEventFlow (borelCantelliToEventFlow x) = some x
    exact BorelCantelliTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BorelCantelliTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance borelCantelliFieldFaithful : FieldFaithful BorelCantelliUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := borelCantelliFields
  field_faithful := BorelCantelliTasteGate_single_carrier_alignment_fields_faithful

instance borelCantelliNontrivial : Nontrivial BorelCantelliUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BorelCantelliUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BorelCantelliUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BorelCantelliUp :=
  -- BEDC touchpoint anchor: BHist BMark
  borelCantelliChapterTasteGate

theorem BorelCantelliTasteGate_single_carrier_alignment :
    (∀ h : BHist, borelCantelliDecodeBHist (borelCantelliEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BorelCantelliUp) ∧
        Nonempty (ChapterTasteGate BorelCantelliUp) ∧
          borelCantelliEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BorelCantelliTasteGate_single_carrier_alignment_decode_encode,
      ⟨borelCantelliBHistCarrier⟩,
      ⟨borelCantelliChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BorelCantelliUp
