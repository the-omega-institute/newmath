import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuasiMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuasiMetricUp : Type where
  | mk : (S X D Z T E H C P N : BHist) → QuasiMetricUp
  deriving DecidableEq

def quasiMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quasiMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quasiMetricEncodeBHist h

def quasiMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quasiMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quasiMetricDecodeBHist tail)

private theorem QuasiMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, quasiMetricDecodeBHist (quasiMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def quasiMetricFields : QuasiMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuasiMetricUp.mk S X D Z T E H C P N => [S, X, D, Z, T, E, H, C, P, N]

def quasiMetricToEventFlow : QuasiMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (quasiMetricFields x).map quasiMetricEncodeBHist

def quasiMetricFromEventFlow : EventFlow → Option QuasiMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | X :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | Z :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
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
                                                (QuasiMetricUp.mk
                                                  (quasiMetricDecodeBHist S)
                                                  (quasiMetricDecodeBHist X)
                                                  (quasiMetricDecodeBHist D)
                                                  (quasiMetricDecodeBHist Z)
                                                  (quasiMetricDecodeBHist T)
                                                  (quasiMetricDecodeBHist E)
                                                  (quasiMetricDecodeBHist H)
                                                  (quasiMetricDecodeBHist C)
                                                  (quasiMetricDecodeBHist P)
                                                  (quasiMetricDecodeBHist N))
                                          | _ :: _ => none

private theorem QuasiMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : QuasiMetricUp, quasiMetricFromEventFlow (quasiMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S X D Z T E H C P N =>
      change
        some
          (QuasiMetricUp.mk
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist S))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist X))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist D))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist Z))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist T))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist E))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist H))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist C))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist P))
            (quasiMetricDecodeBHist (quasiMetricEncodeBHist N))) =
          some (QuasiMetricUp.mk S X D Z T E H C P N)
      rw [QuasiMetricTasteGate_single_carrier_alignment_decode S,
        QuasiMetricTasteGate_single_carrier_alignment_decode X,
        QuasiMetricTasteGate_single_carrier_alignment_decode D,
        QuasiMetricTasteGate_single_carrier_alignment_decode Z,
        QuasiMetricTasteGate_single_carrier_alignment_decode T,
        QuasiMetricTasteGate_single_carrier_alignment_decode E,
        QuasiMetricTasteGate_single_carrier_alignment_decode H,
        QuasiMetricTasteGate_single_carrier_alignment_decode C,
        QuasiMetricTasteGate_single_carrier_alignment_decode P,
        QuasiMetricTasteGate_single_carrier_alignment_decode N]

private theorem QuasiMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : QuasiMetricUp} :
    quasiMetricToEventFlow x = quasiMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quasiMetricFromEventFlow (quasiMetricToEventFlow x) =
        quasiMetricFromEventFlow (quasiMetricToEventFlow y) :=
    congrArg quasiMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (QuasiMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (QuasiMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem QuasiMetricTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : QuasiMetricUp, quasiMetricFields x = quasiMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ X₁ D₁ Z₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ X₂ D₂ Z₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hX tail1
          injection tail1 with hD tail2
          injection tail2 with hZ tail3
          injection tail3 with hT tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hX
          subst hD
          subst hZ
          subst hT
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance quasiMetricBHistCarrier : BHistCarrier QuasiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quasiMetricToEventFlow
  fromEventFlow := quasiMetricFromEventFlow

instance quasiMetricChapterTasteGate : ChapterTasteGate QuasiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quasiMetricFromEventFlow (quasiMetricToEventFlow x) = some x
    exact QuasiMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (QuasiMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance quasiMetricFieldFaithful : FieldFaithful QuasiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := quasiMetricFields
  field_faithful := QuasiMetricTasteGate_single_carrier_alignment_fields_faithful

instance quasiMetricNontrivial : Nontrivial QuasiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuasiMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuasiMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate QuasiMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quasiMetricChapterTasteGate

theorem QuasiMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, quasiMetricDecodeBHist (quasiMetricEncodeBHist h) = h) ∧
      (∀ x : QuasiMetricUp, quasiMetricFromEventFlow (quasiMetricToEventFlow x) = some x) ∧
        (∀ x y : QuasiMetricUp, quasiMetricToEventFlow x = quasiMetricToEventFlow y →
          x = y) ∧
          quasiMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨QuasiMetricTasteGate_single_carrier_alignment_decode,
      QuasiMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => QuasiMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.QuasiMetricUp
