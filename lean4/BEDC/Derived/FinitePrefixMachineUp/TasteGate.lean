import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixMachineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixMachineUp : Type where
  | mk (M Q T F E A H C N : BHist) : FinitePrefixMachineUp
  deriving DecidableEq

def finitePrefixMachineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixMachineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixMachineEncodeBHist h

def finitePrefixMachineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixMachineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixMachineDecodeBHist tail)

private theorem finitePrefixMachineDecode_encode_bhist :
    ∀ h : BHist, finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finitePrefixMachineToEventFlow : FinitePrefixMachineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixMachineUp.mk M Q T F E A H C N =>
      [[BMark.b0],
        finitePrefixMachineEncodeBHist M,
        [BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finitePrefixMachineEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finitePrefixMachineEncodeBHist N]

def finitePrefixMachineFromEventFlow : EventFlow → Option FinitePrefixMachineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restQTag =>
          match restQTag with
          | [] => none
          | _tagQ :: restQ =>
              match restQ with
              | [] => none
              | Q :: restTTag =>
                  match restTTag with
                  | [] => none
                  | _tagT :: restT =>
                      match restT with
                      | [] => none
                      | T :: restFTag =>
                          match restFTag with
                          | [] => none
                          | _tagF :: restF =>
                              match restF with
                              | [] => none
                              | F :: restETag =>
                                  match restETag with
                                  | [] => none
                                  | _tagE :: restE =>
                                      match restE with
                                      | [] => none
                                      | E :: restATag =>
                                          match restATag with
                                          | [] => none
                                          | _tagA :: restA =>
                                              match restA with
                                              | [] => none
                                              | A :: restHTag =>
                                                  match restHTag with
                                                  | [] => none
                                                  | _tagH :: restH =>
                                                      match restH with
                                                      | [] => none
                                                      | H :: restCTag =>
                                                          match restCTag with
                                                          | [] => none
                                                          | _tagC :: restC =>
                                                              match restC with
                                                              | [] => none
                                                              | C :: restNTag =>
                                                                  match restNTag with
                                                                  | [] => none
                                                                  | _tagN :: restN =>
                                                                      match restN with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (FinitePrefixMachineUp.mk
                                                                                  (finitePrefixMachineDecodeBHist M)
                                                                                  (finitePrefixMachineDecodeBHist Q)
                                                                                  (finitePrefixMachineDecodeBHist T)
                                                                                  (finitePrefixMachineDecodeBHist F)
                                                                                  (finitePrefixMachineDecodeBHist E)
                                                                                  (finitePrefixMachineDecodeBHist A)
                                                                                  (finitePrefixMachineDecodeBHist H)
                                                                                  (finitePrefixMachineDecodeBHist C)
                                                                                  (finitePrefixMachineDecodeBHist N))
                                                                          | _ :: _ => none

private theorem finitePrefixMachine_round_trip :
    ∀ x : FinitePrefixMachineUp,
      finitePrefixMachineFromEventFlow (finitePrefixMachineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M Q T F E A H C N =>
      change
        some
          (FinitePrefixMachineUp.mk
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist M))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist Q))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist T))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist F))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist E))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist A))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist H))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist C))
            (finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist N))) =
          some (FinitePrefixMachineUp.mk M Q T F E A H C N)
      rw [finitePrefixMachineDecode_encode_bhist M, finitePrefixMachineDecode_encode_bhist Q,
        finitePrefixMachineDecode_encode_bhist T, finitePrefixMachineDecode_encode_bhist F,
        finitePrefixMachineDecode_encode_bhist E, finitePrefixMachineDecode_encode_bhist A,
        finitePrefixMachineDecode_encode_bhist H, finitePrefixMachineDecode_encode_bhist C,
        finitePrefixMachineDecode_encode_bhist N]

private theorem finitePrefixMachineToEventFlow_injective {x y : FinitePrefixMachineUp} :
    finitePrefixMachineToEventFlow x = finitePrefixMachineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixMachineFromEventFlow (finitePrefixMachineToEventFlow x) =
        finitePrefixMachineFromEventFlow (finitePrefixMachineToEventFlow y) :=
    congrArg finitePrefixMachineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finitePrefixMachine_round_trip x).symm
      (Eq.trans hread (finitePrefixMachine_round_trip y)))

private def finitePrefixMachineFields : FinitePrefixMachineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixMachineUp.mk M Q T F E A H C N => [M, Q, T, F, E, A, H, C, N]

private theorem finitePrefixMachine_fields_faithful :
    ∀ x y : FinitePrefixMachineUp,
      finitePrefixMachineFields x = finitePrefixMachineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 Q1 T1 F1 E1 A1 H1 C1 N1 =>
      cases y with
      | mk M2 Q2 T2 F2 E2 A2 H2 C2 N2 =>
          cases hfields
          rfl

instance finitePrefixMachineBHistCarrier : BHistCarrier FinitePrefixMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixMachineToEventFlow
  fromEventFlow := finitePrefixMachineFromEventFlow

instance finitePrefixMachineChapterTasteGate : ChapterTasteGate FinitePrefixMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finitePrefixMachineFromEventFlow (finitePrefixMachineToEventFlow x) = some x
    exact finitePrefixMachine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finitePrefixMachineToEventFlow_injective heq)

instance finitePrefixMachineFieldFaithful : FieldFaithful FinitePrefixMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finitePrefixMachineFields
  field_faithful := finitePrefixMachine_fields_faithful

instance finitePrefixMachineNontrivial : Nontrivial FinitePrefixMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePrefixMachineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FinitePrefixMachineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FinitePrefixMachineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finitePrefixMachineChapterTasteGate

theorem FinitePrefixMachineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FinitePrefixMachineUp) ∧
      (∀ h : BHist,
        finitePrefixMachineDecodeBHist (finitePrefixMachineEncodeBHist h) = h) ∧
      finitePrefixMachineEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      finitePrefixMachineEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ x : FinitePrefixMachineUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro finitePrefixMachineChapterTasteGate
  constructor
  · exact finitePrefixMachineDecode_encode_bhist
  constructor
  · rfl
  constructor
  · rfl
  · intro x
    change finitePrefixMachineFromEventFlow (finitePrefixMachineToEventFlow x) = some x
    exact finitePrefixMachine_round_trip x

end BEDC.Derived.FinitePrefixMachineUp
