import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineExportBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineExportBoundaryUp : Type where
  | mk : (R T A F H C P N : BHist) → MachineExportBoundaryUp
  deriving DecidableEq

def machineExportBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineExportBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineExportBoundaryEncodeBHist h

def machineExportBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineExportBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineExportBoundaryDecodeBHist tail)

private theorem machineExportBoundaryDecodeEncodeBHist :
    ∀ h : BHist, machineExportBoundaryDecodeBHist
      (machineExportBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def machineExportBoundaryFields : MachineExportBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MachineExportBoundaryUp.mk R T A F H C P N => [R, T, A, F, H, C, P, N]

def machineExportBoundaryToEventFlow : MachineExportBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (machineExportBoundaryFields x).map machineExportBoundaryEncodeBHist

def machineExportBoundaryFromEventFlow : EventFlow → Option MachineExportBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (MachineExportBoundaryUp.mk
                                          (machineExportBoundaryDecodeBHist R)
                                          (machineExportBoundaryDecodeBHist T)
                                          (machineExportBoundaryDecodeBHist A)
                                          (machineExportBoundaryDecodeBHist F)
                                          (machineExportBoundaryDecodeBHist H)
                                          (machineExportBoundaryDecodeBHist C)
                                          (machineExportBoundaryDecodeBHist P)
                                          (machineExportBoundaryDecodeBHist N))
                                  | _ :: _ => none

private theorem machineExportBoundary_round_trip :
    ∀ x : MachineExportBoundaryUp,
      machineExportBoundaryFromEventFlow (machineExportBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R T A F H C P N =>
      change
        some
          (MachineExportBoundaryUp.mk
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist R))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist T))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist A))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist F))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist H))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist C))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist P))
            (machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist N))) =
          some (MachineExportBoundaryUp.mk R T A F H C P N)
      rw [machineExportBoundaryDecodeEncodeBHist R, machineExportBoundaryDecodeEncodeBHist T,
        machineExportBoundaryDecodeEncodeBHist A, machineExportBoundaryDecodeEncodeBHist F,
        machineExportBoundaryDecodeEncodeBHist H, machineExportBoundaryDecodeEncodeBHist C,
        machineExportBoundaryDecodeEncodeBHist P, machineExportBoundaryDecodeEncodeBHist N]

private theorem machineExportBoundaryToEventFlow_injective {x y : MachineExportBoundaryUp} :
    machineExportBoundaryToEventFlow x = machineExportBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      machineExportBoundaryFromEventFlow (machineExportBoundaryToEventFlow x) =
        machineExportBoundaryFromEventFlow (machineExportBoundaryToEventFlow y) :=
    congrArg machineExportBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (machineExportBoundary_round_trip x).symm
      (Eq.trans hread (machineExportBoundary_round_trip y)))

private theorem machineExportBoundary_fields_faithful :
    ∀ x y : MachineExportBoundaryUp,
      machineExportBoundaryFields x = machineExportBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ T₁ A₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ T₂ A₂ F₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hT tail1
          injection tail1 with hA tail2
          injection tail2 with hF tail3
          injection tail3 with hH tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hR
          subst hT
          subst hA
          subst hF
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance machineExportBoundaryBHistCarrier : BHistCarrier MachineExportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineExportBoundaryToEventFlow
  fromEventFlow := machineExportBoundaryFromEventFlow

instance machineExportBoundaryChapterTasteGate :
    ChapterTasteGate MachineExportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change machineExportBoundaryFromEventFlow (machineExportBoundaryToEventFlow x) = some x
    exact machineExportBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineExportBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MachineExportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change machineExportBoundaryFromEventFlow (machineExportBoundaryToEventFlow x) = some x
    exact machineExportBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineExportBoundaryToEventFlow_injective heq)

instance machineExportBoundaryFieldFaithful : FieldFaithful MachineExportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := machineExportBoundaryFields
  field_faithful := machineExportBoundary_fields_faithful

instance machineExportBoundaryNontrivial : Nontrivial MachineExportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineExportBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineExportBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MachineExportBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      machineExportBoundaryDecodeBHist (machineExportBoundaryEncodeBHist h) = h) ∧
      (∀ x : MachineExportBoundaryUp,
        machineExportBoundaryFromEventFlow (machineExportBoundaryToEventFlow x) = some x) ∧
        (∀ x y : MachineExportBoundaryUp,
          machineExportBoundaryToEventFlow x = machineExportBoundaryToEventFlow y → x = y) ∧
          machineExportBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact machineExportBoundaryDecodeEncodeBHist
  · constructor
    · exact machineExportBoundary_round_trip
    · constructor
      · intro x y heq
        exact machineExportBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.MachineExportBoundaryUp
