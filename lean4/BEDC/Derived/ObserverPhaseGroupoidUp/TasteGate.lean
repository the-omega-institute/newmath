import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverPhaseGroupoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverPhaseGroupoidUp : Type where
  | mk (O A S T I M B H C P N : BHist) : ObserverPhaseGroupoidUp
  deriving DecidableEq

def observerPhaseGroupoidEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerPhaseGroupoidEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerPhaseGroupoidEncodeBHist h

def observerPhaseGroupoidDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerPhaseGroupoidDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerPhaseGroupoidDecodeBHist tail)

private theorem observerPhaseGroupoid_decode_encode_bhist :
    ∀ h : BHist,
      observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerPhaseGroupoidFields : ObserverPhaseGroupoidUp → List BHist
  | ObserverPhaseGroupoidUp.mk O A S T I M B H C P N => [O, A, S, T, I, M, B, H, C, P, N]

def observerPhaseGroupoidToEventFlow : ObserverPhaseGroupoidUp → EventFlow
  | x => (observerPhaseGroupoidFields x).map observerPhaseGroupoidEncodeBHist

def observerPhaseGroupoidFromEventFlow : EventFlow → Option ObserverPhaseGroupoidUp
  | [] => none
  | O :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | I :: rest4 =>
                      match rest4 with
                      | [] => none
                      | M :: rest5 =>
                          match rest5 with
                          | [] => none
                          | B :: rest6 =>
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
                                                    (ObserverPhaseGroupoidUp.mk
                                                      (observerPhaseGroupoidDecodeBHist O)
                                                      (observerPhaseGroupoidDecodeBHist A)
                                                      (observerPhaseGroupoidDecodeBHist S)
                                                      (observerPhaseGroupoidDecodeBHist T)
                                                      (observerPhaseGroupoidDecodeBHist I)
                                                      (observerPhaseGroupoidDecodeBHist M)
                                                      (observerPhaseGroupoidDecodeBHist B)
                                                      (observerPhaseGroupoidDecodeBHist H)
                                                      (observerPhaseGroupoidDecodeBHist C)
                                                      (observerPhaseGroupoidDecodeBHist P)
                                                      (observerPhaseGroupoidDecodeBHist N))
                                              | _ :: _ => none

private theorem observerPhaseGroupoid_round_trip :
    ∀ x : ObserverPhaseGroupoidUp,
      observerPhaseGroupoidFromEventFlow (observerPhaseGroupoidToEventFlow x) = some x := by
  intro x
  cases x with
  | mk O A S T I M B H C P N =>
      change
        some
          (ObserverPhaseGroupoidUp.mk
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist O))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist A))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist S))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist T))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist I))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist M))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist B))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist H))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist C))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist P))
            (observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist N))) =
          some (ObserverPhaseGroupoidUp.mk O A S T I M B H C P N)
      rw [observerPhaseGroupoid_decode_encode_bhist O,
        observerPhaseGroupoid_decode_encode_bhist A,
        observerPhaseGroupoid_decode_encode_bhist S,
        observerPhaseGroupoid_decode_encode_bhist T,
        observerPhaseGroupoid_decode_encode_bhist I,
        observerPhaseGroupoid_decode_encode_bhist M,
        observerPhaseGroupoid_decode_encode_bhist B,
        observerPhaseGroupoid_decode_encode_bhist H,
        observerPhaseGroupoid_decode_encode_bhist C,
        observerPhaseGroupoid_decode_encode_bhist P,
        observerPhaseGroupoid_decode_encode_bhist N]

private theorem observerPhaseGroupoidToEventFlow_injective {x y : ObserverPhaseGroupoidUp} :
    observerPhaseGroupoidToEventFlow x = observerPhaseGroupoidToEventFlow y → x = y := by
  intro heq
  have hread :
      observerPhaseGroupoidFromEventFlow (observerPhaseGroupoidToEventFlow x) =
        observerPhaseGroupoidFromEventFlow (observerPhaseGroupoidToEventFlow y) :=
    congrArg observerPhaseGroupoidFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerPhaseGroupoid_round_trip x).symm
      (Eq.trans hread (observerPhaseGroupoid_round_trip y)))

private theorem observerPhaseGroupoid_field_faithful :
    ∀ x y : ObserverPhaseGroupoidUp,
      observerPhaseGroupoidFields x = observerPhaseGroupoidFields y → x = y := by
  intro x y hfields
  cases x with
  | mk O₁ A₁ S₁ T₁ I₁ M₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ A₂ S₂ T₂ I₂ M₂ B₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hO tail0
          injection tail0 with hA tail1
          injection tail1 with hS tail2
          injection tail2 with hT tail3
          injection tail3 with hI tail4
          injection tail4 with hM tail5
          injection tail5 with hB tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hO
          subst hA
          subst hS
          subst hT
          subst hI
          subst hM
          subst hB
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance observerPhaseGroupoidBHistCarrier : BHistCarrier ObserverPhaseGroupoidUp where
  toEventFlow := observerPhaseGroupoidToEventFlow
  fromEventFlow := observerPhaseGroupoidFromEventFlow

instance observerPhaseGroupoidChapterTasteGate : ChapterTasteGate ObserverPhaseGroupoidUp where
  round_trip := by
    intro x
    change observerPhaseGroupoidFromEventFlow (observerPhaseGroupoidToEventFlow x) = some x
    exact observerPhaseGroupoid_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerPhaseGroupoidToEventFlow_injective heq)

instance observerPhaseGroupoidFieldFaithful : FieldFaithful ObserverPhaseGroupoidUp where
  fields := observerPhaseGroupoidFields
  field_faithful := observerPhaseGroupoid_field_faithful

instance observerPhaseGroupoidNontrivial : Nontrivial ObserverPhaseGroupoidUp where
  witness_pair :=
    ⟨ObserverPhaseGroupoidUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverPhaseGroupoidUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverPhaseGroupoidUp :=
  observerPhaseGroupoidChapterTasteGate

theorem ObserverPhaseGroupoidTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerPhaseGroupoidDecodeBHist (observerPhaseGroupoidEncodeBHist h) = h) ∧
      (∀ x : ObserverPhaseGroupoidUp,
        observerPhaseGroupoidFromEventFlow (observerPhaseGroupoidToEventFlow x) = some x) ∧
        (∀ x y : ObserverPhaseGroupoidUp,
          observerPhaseGroupoidToEventFlow x = observerPhaseGroupoidToEventFlow y → x = y) ∧
          observerPhaseGroupoidEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact
    ⟨observerPhaseGroupoid_decode_encode_bhist, observerPhaseGroupoid_round_trip,
      (fun _ _ heq => observerPhaseGroupoidToEventFlow_injective heq), rfl⟩

end BEDC.Derived.ObserverPhaseGroupoidUp
