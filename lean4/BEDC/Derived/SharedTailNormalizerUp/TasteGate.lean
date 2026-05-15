import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SharedTailNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SharedTailNormalizerUp : Type where
  | mk : (A B M W D R F S H C P N : BHist) → SharedTailNormalizerUp
  deriving DecidableEq

private def sharedTailNormalizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sharedTailNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sharedTailNormalizerEncodeBHist h

private def sharedTailNormalizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sharedTailNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sharedTailNormalizerDecodeBHist tail)

private theorem sharedTailNormalizerDecode_encode_bhist :
    ∀ h : BHist,
      sharedTailNormalizerDecodeBHist
        (sharedTailNormalizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sharedTailNormalizerFields : SharedTailNormalizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SharedTailNormalizerUp.mk A B M W D R F S H C P N =>
      [A, B, M, W, D, R, F, S, H, C, P, N]

private def sharedTailNormalizerToEventFlow :
    SharedTailNormalizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sharedTailNormalizerFields x).map sharedTailNormalizerEncodeBHist

private def sharedTailNormalizerFromEventFlow :
    EventFlow → Option SharedTailNormalizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | F :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (SharedTailNormalizerUp.mk
                                                          (sharedTailNormalizerDecodeBHist A)
                                                          (sharedTailNormalizerDecodeBHist B)
                                                          (sharedTailNormalizerDecodeBHist M)
                                                          (sharedTailNormalizerDecodeBHist W)
                                                          (sharedTailNormalizerDecodeBHist D)
                                                          (sharedTailNormalizerDecodeBHist R)
                                                          (sharedTailNormalizerDecodeBHist F)
                                                          (sharedTailNormalizerDecodeBHist S)
                                                          (sharedTailNormalizerDecodeBHist H)
                                                          (sharedTailNormalizerDecodeBHist C)
                                                          (sharedTailNormalizerDecodeBHist P)
                                                          (sharedTailNormalizerDecodeBHist N))
                                                  | _ :: _ => none

private theorem sharedTailNormalizer_round_trip :
    ∀ x : SharedTailNormalizerUp,
      sharedTailNormalizerFromEventFlow
        (sharedTailNormalizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B M W D R F S H C P N =>
      change
        some
          (SharedTailNormalizerUp.mk
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist A))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist B))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist M))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist W))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist D))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist R))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist F))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist S))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist H))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist C))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist P))
            (sharedTailNormalizerDecodeBHist (sharedTailNormalizerEncodeBHist N))) =
          some (SharedTailNormalizerUp.mk A B M W D R F S H C P N)
      rw [sharedTailNormalizerDecode_encode_bhist A,
        sharedTailNormalizerDecode_encode_bhist B,
        sharedTailNormalizerDecode_encode_bhist M,
        sharedTailNormalizerDecode_encode_bhist W,
        sharedTailNormalizerDecode_encode_bhist D,
        sharedTailNormalizerDecode_encode_bhist R,
        sharedTailNormalizerDecode_encode_bhist F,
        sharedTailNormalizerDecode_encode_bhist S,
        sharedTailNormalizerDecode_encode_bhist H,
        sharedTailNormalizerDecode_encode_bhist C,
        sharedTailNormalizerDecode_encode_bhist P,
        sharedTailNormalizerDecode_encode_bhist N]

private theorem sharedTailNormalizerToEventFlow_injective
    {x y : SharedTailNormalizerUp} :
    sharedTailNormalizerToEventFlow x =
      sharedTailNormalizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sharedTailNormalizerFromEventFlow
          (sharedTailNormalizerToEventFlow x) =
        sharedTailNormalizerFromEventFlow
          (sharedTailNormalizerToEventFlow y) :=
    congrArg sharedTailNormalizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sharedTailNormalizer_round_trip x).symm
      (Eq.trans hread (sharedTailNormalizer_round_trip y)))

private theorem sharedTailNormalizer_fields_faithful :
    ∀ x y : SharedTailNormalizerUp,
      sharedTailNormalizerFields x = sharedTailNormalizerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ M₁ W₁ D₁ R₁ F₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ M₂ W₂ D₂ R₂ F₂ S₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA tailA
          injection tailA with hB tailB
          injection tailB with hM tailM
          injection tailM with hW tailW
          injection tailW with hD tailD
          injection tailD with hR tailR
          injection tailR with hF tailF
          injection tailF with hS tailS
          injection tailS with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          subst hA
          subst hB
          subst hM
          subst hW
          subst hD
          subst hR
          subst hF
          subst hS
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance sharedTailNormalizerBHistCarrier :
    BHistCarrier SharedTailNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sharedTailNormalizerToEventFlow
  fromEventFlow := sharedTailNormalizerFromEventFlow

instance sharedTailNormalizerChapterTasteGate :
    ChapterTasteGate SharedTailNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sharedTailNormalizerFromEventFlow
      (sharedTailNormalizerToEventFlow x) = some x
    exact sharedTailNormalizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sharedTailNormalizerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SharedTailNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sharedTailNormalizerFromEventFlow
      (sharedTailNormalizerToEventFlow x) = some x
    exact sharedTailNormalizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sharedTailNormalizerToEventFlow_injective heq)

instance sharedTailNormalizerFieldFaithful :
    FieldFaithful SharedTailNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sharedTailNormalizerFields
  field_faithful := sharedTailNormalizer_fields_faithful

instance sharedTailNormalizerNontrivial :
    Nontrivial SharedTailNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SharedTailNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SharedTailNormalizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SharedTailNormalizerTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SharedTailNormalizerUp) ∧
      Nonempty (ChapterTasteGate SharedTailNormalizerUp) ∧
        Nonempty (FieldFaithful SharedTailNormalizerUp) ∧
          Nonempty (Nontrivial SharedTailNormalizerUp) ∧
            sharedTailNormalizerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              sharedTailNormalizerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact ⟨sharedTailNormalizerBHistCarrier⟩
  · constructor
    · exact ⟨sharedTailNormalizerChapterTasteGate⟩
    · constructor
      · exact ⟨sharedTailNormalizerFieldFaithful⟩
      · constructor
        · exact ⟨sharedTailNormalizerNontrivial⟩
        · constructor
          · rfl
          · rfl

theorem SharedTailNormalizerCarrier_common_route_alignment
    (x : SharedTailNormalizerUp) :
    ∃ A B M W D R F S H C P N : BHist,
      sharedTailNormalizerFields x = [A, B, M, W, D, R, F, S, H, C, P, N] ∧
        Cont A M (append A M) ∧
          Cont B M (append B M) ∧
            Cont M W (append M W) ∧
              Cont W D (append W D) ∧
                Cont D R (append D R) ∧
                  Cont R F (append R F) ∧
                    Cont F S (append F S) ∧
                      sharedTailNormalizerFromEventFlow
                        (sharedTailNormalizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist Cont
  cases x with
  | mk A B M W D R F S H C P N =>
      refine ⟨A, B, M, W, D, R, F, S, H, C, P, N, ?_⟩
      constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor
                  · rfl
                  · constructor
                    · rfl
                    · exact sharedTailNormalizer_round_trip
                        (SharedTailNormalizerUp.mk A B M W D R F S H C P N)

end BEDC.Derived.SharedTailNormalizerUp
