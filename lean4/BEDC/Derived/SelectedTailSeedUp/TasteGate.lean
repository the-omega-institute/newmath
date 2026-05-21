import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SelectedTailSeedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SelectedTailSeedUp : Type where
  | mk : (Q E A W K S R H C P N : BHist) → SelectedTailSeedUp
  deriving DecidableEq

def selectedTailSeedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: selectedTailSeedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: selectedTailSeedEncodeBHist h

def selectedTailSeedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (selectedTailSeedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (selectedTailSeedDecodeBHist tail)

private theorem selectedTailSeedDecode_encode_bhist :
    ∀ h : BHist, selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def selectedTailSeedToEventFlow : SelectedTailSeedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SelectedTailSeedUp.mk Q E A W K S R H C P N =>
      [[BMark.b0],
        selectedTailSeedEncodeBHist Q,
        [BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        selectedTailSeedEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selectedTailSeedEncodeBHist N]

def selectedTailSeedFromEventFlow : EventFlow → Option SelectedTailSeedUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | K :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | S :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | R :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (SelectedTailSeedUp.mk
                                                                                                  (selectedTailSeedDecodeBHist Q)
                                                                                                  (selectedTailSeedDecodeBHist E)
                                                                                                  (selectedTailSeedDecodeBHist A)
                                                                                                  (selectedTailSeedDecodeBHist W)
                                                                                                  (selectedTailSeedDecodeBHist K)
                                                                                                  (selectedTailSeedDecodeBHist S)
                                                                                                  (selectedTailSeedDecodeBHist R)
                                                                                                  (selectedTailSeedDecodeBHist H)
                                                                                                  (selectedTailSeedDecodeBHist C)
                                                                                                  (selectedTailSeedDecodeBHist P)
                                                                                                  (selectedTailSeedDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem selectedTailSeed_round_trip :
    ∀ x : SelectedTailSeedUp,
      selectedTailSeedFromEventFlow (selectedTailSeedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q E A W K S R H C P N =>
      change
        some
          (SelectedTailSeedUp.mk
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist Q))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist E))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist A))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist W))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist K))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist S))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist R))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist H))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist C))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist P))
            (selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist N))) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N)
      rw [selectedTailSeedDecode_encode_bhist Q, selectedTailSeedDecode_encode_bhist E,
        selectedTailSeedDecode_encode_bhist A, selectedTailSeedDecode_encode_bhist W,
        selectedTailSeedDecode_encode_bhist K, selectedTailSeedDecode_encode_bhist S,
        selectedTailSeedDecode_encode_bhist R, selectedTailSeedDecode_encode_bhist H,
        selectedTailSeedDecode_encode_bhist C, selectedTailSeedDecode_encode_bhist P,
        selectedTailSeedDecode_encode_bhist N]

private theorem selectedTailSeedToEventFlow_injective {x y : SelectedTailSeedUp} :
    selectedTailSeedToEventFlow x = selectedTailSeedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      selectedTailSeedFromEventFlow (selectedTailSeedToEventFlow x) =
        selectedTailSeedFromEventFlow (selectedTailSeedToEventFlow y) :=
    congrArg selectedTailSeedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (selectedTailSeed_round_trip x).symm
      (Eq.trans hread (selectedTailSeed_round_trip y)))

instance selectedTailSeedBHistCarrier : BHistCarrier SelectedTailSeedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := selectedTailSeedToEventFlow
  fromEventFlow := selectedTailSeedFromEventFlow

instance selectedTailSeedChapterTasteGate : ChapterTasteGate SelectedTailSeedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change selectedTailSeedFromEventFlow (selectedTailSeedToEventFlow x) = some x
    exact selectedTailSeed_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (selectedTailSeedToEventFlow_injective heq)

instance selectedTailSeedFieldFaithful : FieldFaithful SelectedTailSeedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SelectedTailSeedUp.mk Q E A W K S R H C P N => [Q, E, A, W, K, S, R, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk Q₁ E₁ A₁ W₁ K₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk Q₂ E₂ A₂ W₂ K₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
            injection h with hQ t1
            injection t1 with hE t2
            injection t2 with hA t3
            injection t3 with hW t4
            injection t4 with hK t5
            injection t5 with hS t6
            injection t6 with hR t7
            injection t7 with hH t8
            injection t8 with hC t9
            injection t9 with hP t10
            injection t10 with hN _
            cases hQ
            cases hE
            cases hA
            cases hW
            cases hK
            cases hS
            cases hR
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance selectedTailSeedNontrivial : Nontrivial SelectedTailSeedUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SelectedTailSeedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SelectedTailSeedUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SelectedTailSeedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem SelectedTailSeedTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SelectedTailSeedUp) ∧
      Nonempty (FieldFaithful SelectedTailSeedUp) ∧
        Nonempty (Nontrivial SelectedTailSeedUp) ∧
          (∀ h : BHist, selectedTailSeedDecodeBHist (selectedTailSeedEncodeBHist h) = h) ∧
            (∀ x : SelectedTailSeedUp,
              selectedTailSeedFromEventFlow (selectedTailSeedToEventFlow x) = some x) ∧
              (∀ x y : SelectedTailSeedUp,
                selectedTailSeedToEventFlow x = selectedTailSeedToEventFlow y → x = y) ∧
                selectedTailSeedEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro selectedTailSeedChapterTasteGate,
      Nonempty.intro selectedTailSeedFieldFaithful,
      Nonempty.intro selectedTailSeedNontrivial,
      selectedTailSeedDecode_encode_bhist,
      selectedTailSeed_round_trip,
      (fun _ _ heq => selectedTailSeedToEventFlow_injective heq),
      rfl⟩

theorem SelectedTailSeedCarrier_classifier_transport
    {Q E A W K S R H C P N K' : BHist} (route : Cont A W K)
    (sameReadback : hsame K K') :
    Cont A W K' ∧
      BHistCarrier.fromEventFlow
        (BHistCarrier.toEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases sameReadback
  constructor
  · exact route
  · change
      selectedTailSeedFromEventFlow
        (selectedTailSeedToEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N)
    exact selectedTailSeed_round_trip (SelectedTailSeedUp.mk Q E A W K S R H C P N)

theorem SelectedTailSeedCarrier_finite_tail_admission_exactness
    {Q E A W K S R H C P N W' K' : BHist} (sameWindow : hsame W W')
    (admission : Cont A W K) (readback : Cont A W' K') :
    hsame K K' ∧
      BHistCarrier.fromEventFlow
        (BHistCarrier.toEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · exact cont_respects_hsame (hsame_refl A) sameWindow admission readback
  · change
      selectedTailSeedFromEventFlow
        (selectedTailSeedToEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N)
    exact selectedTailSeed_round_trip (SelectedTailSeedUp.mk Q E A W K S R H C P N)

theorem SelectedTailSeedCarrier_endpoint_exactness_readback_stability
    {Q E A W K S R H C P N E' : BHist} (windowUnary : UnaryHistory W)
    (readbackUnary : UnaryHistory K) (sameEndpoint : hsame E E')
    (endpointRoute : Cont Q E W) (readbackRoute : Cont W K S) :
    Cont Q E' W ∧ UnaryHistory S ∧
      BHistCarrier.fromEventFlow
          (BHistCarrier.toEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
        some (SelectedTailSeedUp.mk Q E A W K S R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  have transportedEndpoint : Cont Q E' W :=
    cont_hsame_transport (hsame_refl Q) sameEndpoint (hsame_refl W) endpointRoute
  have readbackClosed : UnaryHistory S :=
    unary_cont_closed windowUnary readbackUnary readbackRoute
  constructor
  · exact transportedEndpoint
  · constructor
    · exact readbackClosed
    · change
        selectedTailSeedFromEventFlow
            (selectedTailSeedToEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N)
      exact selectedTailSeed_round_trip (SelectedTailSeedUp.mk Q E A W K S R H C P N)

theorem SelectedTailSeedCarrier_real_window_handoff {Q E A W K S R H C P N : BHist} :
    BHistCarrier.fromEventFlow
          (BHistCarrier.toEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
        some (SelectedTailSeedUp.mk Q E A W K S R H C P N) ∧
      Cont R N (append R N) ∧ hsame (append R N) (append R N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · change
      selectedTailSeedFromEventFlow
          (selectedTailSeedToEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
        some (SelectedTailSeedUp.mk Q E A W K S R H C P N)
    exact selectedTailSeed_round_trip (SelectedTailSeedUp.mk Q E A W K S R H C P N)
  · constructor
    · exact cont_intro rfl
    · exact hsame_refl (append R N)

theorem SelectedTailSeedWindowReadbackCoherence {Q E A W K S R H C P N : BHist}
    (windowUnary : UnaryHistory W) (readbackUnary : UnaryHistory K)
    (realSealUnary : UnaryHistory R) (windowReadback : Cont W K S) :
    UnaryHistory S ∧ UnaryHistory (append S R) ∧ Cont W K S ∧
      Cont S R (append S R) ∧
        BHistCarrier.fromEventFlow
            (BHistCarrier.toEventFlow (SelectedTailSeedUp.mk Q E A W K S R H C P N)) =
          some (SelectedTailSeedUp.mk Q E A W K S R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  have ledgerUnary : UnaryHistory S :=
    unary_cont_closed windowUnary readbackUnary windowReadback
  have replay : Cont S R (append S R) := cont_intro rfl
  have sealedUnary : UnaryHistory (append S R) :=
    unary_cont_closed ledgerUnary realSealUnary replay
  exact
    ⟨ledgerUnary, sealedUnary, windowReadback, replay,
      selectedTailSeed_round_trip (SelectedTailSeedUp.mk Q E A W K S R H C P N)⟩

end BEDC.Derived.SelectedTailSeedUp
