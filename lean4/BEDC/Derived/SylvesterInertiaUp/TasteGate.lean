import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SylvesterInertiaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SylvesterInertiaUp : Type where
  | mk
      (fieldSource matrixPresentation bilinearForm quadraticForm diagonalWitness signCountLedger
        transport replay provenance localNameCert : BHist) :
        SylvesterInertiaUp
  deriving DecidableEq

def sylvesterInertiaTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0, BMark.b0]

def sylvesterInertiaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sylvesterInertiaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sylvesterInertiaEncodeBHist h

def sylvesterInertiaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sylvesterInertiaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sylvesterInertiaDecodeBHist tail)

private theorem sylvesterInertiaDecode_encode :
    ∀ h : BHist, sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sylvesterInertiaToEventFlow : SylvesterInertiaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SylvesterInertiaUp.mk fieldSource matrixPresentation bilinearForm quadraticForm
      diagonalWitness signCountLedger transport replay provenance localNameCert =>
      [sylvesterInertiaTag,
        sylvesterInertiaEncodeBHist fieldSource,
        sylvesterInertiaEncodeBHist matrixPresentation,
        sylvesterInertiaEncodeBHist bilinearForm,
        sylvesterInertiaEncodeBHist quadraticForm,
        sylvesterInertiaEncodeBHist diagonalWitness,
        sylvesterInertiaEncodeBHist signCountLedger,
        sylvesterInertiaEncodeBHist transport,
        sylvesterInertiaEncodeBHist replay,
        sylvesterInertiaEncodeBHist provenance,
        sylvesterInertiaEncodeBHist localNameCert]

private def sylvesterInertiaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sylvesterInertiaEventAt index rest

def sylvesterInertiaFromEventFlow : EventFlow → Option SylvesterInertiaUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SylvesterInertiaUp.mk
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 1 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 2 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 3 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 4 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 5 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 6 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 7 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 8 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 9 ef))
          (sylvesterInertiaDecodeBHist (sylvesterInertiaEventAt 10 ef)))

private theorem sylvesterInertia_round_trip :
    ∀ x : SylvesterInertiaUp,
      sylvesterInertiaFromEventFlow (sylvesterInertiaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fieldSource matrixPresentation bilinearForm quadraticForm diagonalWitness
      signCountLedger transport replay provenance localNameCert =>
      change
        some
          (SylvesterInertiaUp.mk
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist fieldSource))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist matrixPresentation))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist bilinearForm))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist quadraticForm))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist diagonalWitness))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist signCountLedger))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist transport))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist replay))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist provenance))
            (sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist localNameCert))) =
          some
            (SylvesterInertiaUp.mk fieldSource matrixPresentation bilinearForm quadraticForm
              diagonalWitness signCountLedger transport replay provenance localNameCert)
      rw [sylvesterInertiaDecode_encode fieldSource,
        sylvesterInertiaDecode_encode matrixPresentation,
        sylvesterInertiaDecode_encode bilinearForm,
        sylvesterInertiaDecode_encode quadraticForm,
        sylvesterInertiaDecode_encode diagonalWitness,
        sylvesterInertiaDecode_encode signCountLedger,
        sylvesterInertiaDecode_encode transport,
        sylvesterInertiaDecode_encode replay,
        sylvesterInertiaDecode_encode provenance,
        sylvesterInertiaDecode_encode localNameCert]

private theorem sylvesterInertiaToEventFlow_injective {x y : SylvesterInertiaUp} :
    sylvesterInertiaToEventFlow x = sylvesterInertiaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sylvesterInertiaFromEventFlow (sylvesterInertiaToEventFlow x) =
        sylvesterInertiaFromEventFlow (sylvesterInertiaToEventFlow y) :=
    congrArg sylvesterInertiaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sylvesterInertia_round_trip x).symm
      (Eq.trans hread (sylvesterInertia_round_trip y)))

instance SylvesterInertiaTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier SylvesterInertiaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sylvesterInertiaToEventFlow
  fromEventFlow := sylvesterInertiaFromEventFlow

instance SylvesterInertiaTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate SylvesterInertiaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sylvesterInertiaFromEventFlow (sylvesterInertiaToEventFlow x) = some x
    exact sylvesterInertia_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sylvesterInertiaToEventFlow_injective heq)

def SylvesterInertiaTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SylvesterInertiaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SylvesterInertiaTasteGate_single_carrier_alignment_ChapterTasteGate

theorem SylvesterInertiaTasteGate_single_carrier_alignment :
    (∀ h : BHist, sylvesterInertiaDecodeBHist (sylvesterInertiaEncodeBHist h) = h) ∧
      (∀ x : SylvesterInertiaUp,
        sylvesterInertiaFromEventFlow (sylvesterInertiaToEventFlow x) = some x) ∧
      (∀ x y : SylvesterInertiaUp,
        sylvesterInertiaToEventFlow x = sylvesterInertiaToEventFlow y → x = y) ∧
      sylvesterInertiaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact sylvesterInertiaDecode_encode
  · constructor
    · exact sylvesterInertia_round_trip
    · constructor
      · intro x y heq
        exact sylvesterInertiaToEventFlow_injective heq
      · rfl

end BEDC.Derived.SylvesterInertiaUp
