import BEDC.Derived.AffineVarUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AffineVarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AffineVarUp : Type where
  | mk (family point equationRow zeroWitness localNameCert : BHist) : AffineVarUp
  deriving DecidableEq

def affineVarTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def affineVarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: affineVarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: affineVarEncodeBHist h

def affineVarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (affineVarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (affineVarDecodeBHist tail)

private theorem affineVarDecodeEncodeBHist :
    ∀ h : BHist, affineVarDecodeBHist (affineVarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def affineVarFields : AffineVarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AffineVarUp.mk family point equationRow zeroWitness localNameCert =>
      [family, point, equationRow, zeroWitness, localNameCert]

def affineVarToEventFlow : AffineVarUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AffineVarUp.mk family point equationRow zeroWitness localNameCert =>
      [affineVarTag, affineVarEncodeBHist family, affineVarEncodeBHist point,
        affineVarEncodeBHist equationRow, affineVarEncodeBHist zeroWitness,
        affineVarEncodeBHist localNameCert]

private def affineVarEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => affineVarEventAt index rest

def affineVarFromEventFlow : EventFlow → Option AffineVarUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (AffineVarUp.mk
          (affineVarDecodeBHist (affineVarEventAt 1 ef))
          (affineVarDecodeBHist (affineVarEventAt 2 ef))
          (affineVarDecodeBHist (affineVarEventAt 3 ef))
          (affineVarDecodeBHist (affineVarEventAt 4 ef))
          (affineVarDecodeBHist (affineVarEventAt 5 ef)))

private theorem affineVarRoundTrip :
    ∀ x : AffineVarUp, affineVarFromEventFlow (affineVarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family point equationRow zeroWitness localNameCert =>
      change
        some
          (AffineVarUp.mk
            (affineVarDecodeBHist (affineVarEncodeBHist family))
            (affineVarDecodeBHist (affineVarEncodeBHist point))
            (affineVarDecodeBHist (affineVarEncodeBHist equationRow))
            (affineVarDecodeBHist (affineVarEncodeBHist zeroWitness))
            (affineVarDecodeBHist (affineVarEncodeBHist localNameCert))) =
          some (AffineVarUp.mk family point equationRow zeroWitness localNameCert)
      rw [affineVarDecodeEncodeBHist family, affineVarDecodeEncodeBHist point,
        affineVarDecodeEncodeBHist equationRow, affineVarDecodeEncodeBHist zeroWitness,
        affineVarDecodeEncodeBHist localNameCert]

private theorem affineVarToEventFlow_injective {x y : AffineVarUp} :
    affineVarToEventFlow x = affineVarToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      affineVarFromEventFlow (affineVarToEventFlow x) =
        affineVarFromEventFlow (affineVarToEventFlow y) :=
    congrArg affineVarFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (affineVarRoundTrip x).symm (Eq.trans hread (affineVarRoundTrip y)))

private theorem affineVarFields_faithful :
    ∀ x y : AffineVarUp, affineVarFields x = affineVarFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk family₁ point₁ equationRow₁ zeroWitness₁ localNameCert₁ =>
      cases y with
      | mk family₂ point₂ equationRow₂ zeroWitness₂ localNameCert₂ =>
          cases hfields
          rfl

instance affineVarBHistCarrier : BHistCarrier AffineVarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := affineVarToEventFlow
  fromEventFlow := affineVarFromEventFlow

instance affineVarChapterTasteGate : ChapterTasteGate AffineVarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change affineVarFromEventFlow (affineVarToEventFlow x) = some x
    exact affineVarRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (affineVarToEventFlow_injective heq)

instance affineVarFieldFaithful : FieldFaithful AffineVarUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := affineVarFields
  field_faithful := affineVarFields_faithful

theorem AffineVarTasteGate_single_carrier_alignment :
    (∀ h : BHist, affineVarDecodeBHist (affineVarEncodeBHist h) = h) ∧
      (∀ x : AffineVarUp, affineVarFromEventFlow (affineVarToEventFlow x) = some x) ∧
        (∀ x y : AffineVarUp, affineVarToEventFlow x = affineVarToEventFlow y -> x = y) ∧
          affineVarEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨affineVarDecodeEncodeBHist,
      ⟨affineVarRoundTrip, ⟨fun _ _ heq => affineVarToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.AffineVarUp
