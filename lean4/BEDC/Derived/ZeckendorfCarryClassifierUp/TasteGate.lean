import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZeckendorfCarryClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZeckendorfCarryClassifierUp : Type where
  | mk :
      (source target carry sourceNormal targetNormal separated readback provenance name : BHist) →
      ZeckendorfCarryClassifierUp
  deriving DecidableEq

def zeckendorfCarryClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zeckendorfCarryClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zeckendorfCarryClassifierEncodeBHist h

def zeckendorfCarryClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zeckendorfCarryClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zeckendorfCarryClassifierDecodeBHist tail)

private theorem zeckendorfCarryClassifier_decode_encode_bhist :
    ∀ h : BHist,
      zeckendorfCarryClassifierDecodeBHist
          (zeckendorfCarryClassifierEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def zeckendorfCarryClassifierFields :
    ZeckendorfCarryClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZeckendorfCarryClassifierUp.mk source target carry sourceNormal targetNormal separated
      readback provenance name =>
      [source, target, carry, sourceNormal, targetNormal, separated, readback, provenance, name]

def zeckendorfCarryClassifierToEventFlow :
    ZeckendorfCarryClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (zeckendorfCarryClassifierFields x).map zeckendorfCarryClassifierEncodeBHist

def zeckendorfCarryClassifierFromEventFlow :
    EventFlow → Option ZeckendorfCarryClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | source :: target :: carry :: sourceNormal :: targetNormal :: separated :: readback ::
      provenance :: name :: [] =>
      some
        (ZeckendorfCarryClassifierUp.mk
          (zeckendorfCarryClassifierDecodeBHist source)
          (zeckendorfCarryClassifierDecodeBHist target)
          (zeckendorfCarryClassifierDecodeBHist carry)
          (zeckendorfCarryClassifierDecodeBHist sourceNormal)
          (zeckendorfCarryClassifierDecodeBHist targetNormal)
          (zeckendorfCarryClassifierDecodeBHist separated)
          (zeckendorfCarryClassifierDecodeBHist readback)
          (zeckendorfCarryClassifierDecodeBHist provenance)
          (zeckendorfCarryClassifierDecodeBHist name))
  | _ => none

private theorem zeckendorfCarryClassifier_round_trip :
    ∀ x : ZeckendorfCarryClassifierUp,
      zeckendorfCarryClassifierFromEventFlow
          (zeckendorfCarryClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target carry sourceNormal targetNormal separated readback provenance name =>
      simp only [zeckendorfCarryClassifierToEventFlow, zeckendorfCarryClassifierFields,
        zeckendorfCarryClassifierFromEventFlow, List.map_cons, List.map_nil,
        zeckendorfCarryClassifier_decode_encode_bhist]

private theorem zeckendorfCarryClassifierToEventFlow_injective
    {x y : ZeckendorfCarryClassifierUp} :
    zeckendorfCarryClassifierToEventFlow x =
        zeckendorfCarryClassifierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zeckendorfCarryClassifierFromEventFlow
          (zeckendorfCarryClassifierToEventFlow x) =
        zeckendorfCarryClassifierFromEventFlow
          (zeckendorfCarryClassifierToEventFlow y) :=
    congrArg zeckendorfCarryClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zeckendorfCarryClassifier_round_trip x).symm
      (Eq.trans hread (zeckendorfCarryClassifier_round_trip y)))

instance zeckendorfCarryClassifierBHistCarrier :
    BHistCarrier ZeckendorfCarryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zeckendorfCarryClassifierToEventFlow
  fromEventFlow := zeckendorfCarryClassifierFromEventFlow

instance zeckendorfCarryClassifierChapterTasteGate :
    ChapterTasteGate ZeckendorfCarryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      zeckendorfCarryClassifierFromEventFlow
          (zeckendorfCarryClassifierToEventFlow x) =
        some x
    exact zeckendorfCarryClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zeckendorfCarryClassifierToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ZeckendorfCarryClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  zeckendorfCarryClassifierChapterTasteGate

namespace TasteGate

theorem ZeckendorfCarryClassifierTasteGate_single_carrier_alignment
    (x : ZeckendorfCarryClassifierUp) :
    (exists u v c s t h r p n : BHist,
        x = ZeckendorfCarryClassifierUp.mk u v c s t h r p n ∧
          zeckendorfCarryClassifierFields x = [u, v, c, s, t, h, r, p, n] ∧
          zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist u) =
            u ∧
          zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist v) =
            v) ∧
      zeckendorfCarryClassifierEncodeBHist (BHist.e0 (BHist.e1 BHist.Empty)) =
        [BMark.b0, BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  cases x with
  | mk u v c s t h r p n =>
      constructor
      · exact
          ⟨u, v, c, s, t, h, r, p, n, rfl, rfl,
            zeckendorfCarryClassifier_decode_encode_bhist u,
            zeckendorfCarryClassifier_decode_encode_bhist v⟩
      · rfl

end TasteGate

end BEDC.Derived.ZeckendorfCarryClassifierUp
