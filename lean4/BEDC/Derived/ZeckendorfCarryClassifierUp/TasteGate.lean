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
      (source target carry sourceNormal targetNormal separation readback provenance
        name : BHist) →
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

private theorem zeckendorfCarryClassifierDecodeEncode :
    ∀ h : BHist,
      zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def zeckendorfCarryClassifierFields : ZeckendorfCarryClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZeckendorfCarryClassifierUp.mk source target carry sourceNormal targetNormal separation
      readback provenance name =>
      [source, target, carry, sourceNormal, targetNormal, separation, readback, provenance, name]

def zeckendorfCarryClassifierToEventFlow : ZeckendorfCarryClassifierUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (zeckendorfCarryClassifierFields x).map zeckendorfCarryClassifierEncodeBHist

private def zeckendorfCarryClassifierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => zeckendorfCarryClassifierEventAtDefault index rest

def zeckendorfCarryClassifierFromEventFlow
    (ef : EventFlow) : Option ZeckendorfCarryClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ZeckendorfCarryClassifierUp.mk
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 0 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 1 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 2 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 3 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 4 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 5 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 6 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 7 ef))
      (zeckendorfCarryClassifierDecodeBHist (zeckendorfCarryClassifierEventAtDefault 8 ef)))

private theorem zeckendorfCarryClassifierRoundTrip :
    ∀ x : ZeckendorfCarryClassifierUp,
      zeckendorfCarryClassifierFromEventFlow
        (zeckendorfCarryClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target carry sourceNormal targetNormal separation readback provenance name =>
      change
        some
          (ZeckendorfCarryClassifierUp.mk
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist source))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist target))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist carry))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist sourceNormal))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist targetNormal))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist separation))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist readback))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist provenance))
            (zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist name))) =
          some
            (ZeckendorfCarryClassifierUp.mk source target carry sourceNormal targetNormal
              separation readback provenance name)
      rw [zeckendorfCarryClassifierDecodeEncode source,
        zeckendorfCarryClassifierDecodeEncode target,
        zeckendorfCarryClassifierDecodeEncode carry,
        zeckendorfCarryClassifierDecodeEncode sourceNormal,
        zeckendorfCarryClassifierDecodeEncode targetNormal,
        zeckendorfCarryClassifierDecodeEncode separation,
        zeckendorfCarryClassifierDecodeEncode readback,
        zeckendorfCarryClassifierDecodeEncode provenance,
        zeckendorfCarryClassifierDecodeEncode name]

private theorem zeckendorfCarryClassifierToEventFlow_injective
    {x y : ZeckendorfCarryClassifierUp} :
    zeckendorfCarryClassifierToEventFlow x = zeckendorfCarryClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zeckendorfCarryClassifierFromEventFlow (zeckendorfCarryClassifierToEventFlow x) =
        zeckendorfCarryClassifierFromEventFlow (zeckendorfCarryClassifierToEventFlow y) :=
    congrArg zeckendorfCarryClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zeckendorfCarryClassifierRoundTrip x).symm
      (Eq.trans hread (zeckendorfCarryClassifierRoundTrip y)))

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
      zeckendorfCarryClassifierFromEventFlow (zeckendorfCarryClassifierToEventFlow x) =
        some x
    exact zeckendorfCarryClassifierRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zeckendorfCarryClassifierToEventFlow_injective heq)

instance zeckendorfCarryClassifierNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ZeckendorfCarryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ZeckendorfCarryClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ZeckendorfCarryClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ZeckendorfCarryClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  zeckendorfCarryClassifierChapterTasteGate

theorem ZeckendorfCarryClassifierTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ZeckendorfCarryClassifierUp) ∧
      Nonempty (ChapterTasteGate ZeckendorfCarryClassifierUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ZeckendorfCarryClassifierUp) ∧
          (∀ h : BHist,
            zeckendorfCarryClassifierDecodeBHist
              (zeckendorfCarryClassifierEncodeBHist h) = h) ∧
            (∀ x : ZeckendorfCarryClassifierUp,
              zeckendorfCarryClassifierFromEventFlow
                (zeckendorfCarryClassifierToEventFlow x) = some x) ∧
              (∀ x y : ZeckendorfCarryClassifierUp,
                zeckendorfCarryClassifierToEventFlow x =
                  zeckendorfCarryClassifierToEventFlow y → x = y) ∧
                zeckendorfCarryClassifierEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨zeckendorfCarryClassifierBHistCarrier⟩,
      ⟨zeckendorfCarryClassifierChapterTasteGate⟩,
      ⟨zeckendorfCarryClassifierNontrivial⟩,
      zeckendorfCarryClassifierDecodeEncode,
      zeckendorfCarryClassifierRoundTrip,
      (fun _ _ heq => zeckendorfCarryClassifierToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ZeckendorfCarryClassifierUp
