import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArgumentPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArgumentPrincipleUp : Type where
  | mk :
      (contour holomorphic zeroLedger poleLedger winding integral residue reparam
        transport replay provenance name : BHist) →
        ArgumentPrincipleUp
  deriving DecidableEq

def argumentPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: argumentPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: argumentPrincipleEncodeBHist h

def argumentPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (argumentPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (argumentPrincipleDecodeBHist tail)

theorem argumentPrincipleDecodeEncodeBHist :
    ∀ h : BHist, argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def argumentPrincipleFields : ArgumentPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArgumentPrincipleUp.mk contour holomorphic zeroLedger poleLedger winding integral residue
      reparam transport replay provenance name =>
      [contour, holomorphic, zeroLedger, poleLedger, winding, integral, residue, reparam,
        transport, replay, provenance, name]

theorem argumentPrincipleMkCongr
    {contour contour' holomorphic holomorphic' zeroLedger zeroLedger'
      poleLedger poleLedger' winding winding' integral integral' residue residue'
      reparam reparam' transport transport' replay replay' provenance provenance' name name' :
        BHist}
    (hContour : contour' = contour)
    (hHolomorphic : holomorphic' = holomorphic)
    (hZeroLedger : zeroLedger' = zeroLedger)
    (hPoleLedger : poleLedger' = poleLedger)
    (hWinding : winding' = winding)
    (hIntegral : integral' = integral)
    (hResidue : residue' = residue)
    (hReparam : reparam' = reparam)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ArgumentPrincipleUp.mk contour' holomorphic' zeroLedger' poleLedger' winding'
        integral' residue' reparam' transport' replay' provenance' name' =
      ArgumentPrincipleUp.mk contour holomorphic zeroLedger poleLedger winding integral residue
        reparam transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hContour
  cases hHolomorphic
  cases hZeroLedger
  cases hPoleLedger
  cases hWinding
  cases hIntegral
  cases hResidue
  cases hReparam
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def argumentPrincipleToEventFlow : ArgumentPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (argumentPrincipleFields x).map argumentPrincipleEncodeBHist

private def argumentPrincipleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => argumentPrincipleEventAt index rest

def argumentPrincipleFromEventFlow (ef : EventFlow) : Option ArgumentPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArgumentPrincipleUp.mk
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 0 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 1 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 2 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 3 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 4 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 5 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 6 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 7 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 8 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 9 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 10 ef))
      (argumentPrincipleDecodeBHist (argumentPrincipleEventAt 11 ef)))

theorem argumentPrincipleRoundTrip :
    ∀ x : ArgumentPrincipleUp,
      argumentPrincipleFromEventFlow (argumentPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk contour holomorphic zeroLedger poleLedger winding integral residue reparam transport
      replay provenance name =>
      change
        some
          (ArgumentPrincipleUp.mk
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist contour))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist holomorphic))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist zeroLedger))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist poleLedger))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist winding))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist integral))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist residue))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist reparam))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist transport))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist replay))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist provenance))
            (argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist name))) =
          some
            (ArgumentPrincipleUp.mk contour holomorphic zeroLedger poleLedger winding integral
              residue reparam transport replay provenance name)
      rw [argumentPrincipleDecodeEncodeBHist contour,
        argumentPrincipleDecodeEncodeBHist holomorphic,
        argumentPrincipleDecodeEncodeBHist zeroLedger,
        argumentPrincipleDecodeEncodeBHist poleLedger,
        argumentPrincipleDecodeEncodeBHist winding,
        argumentPrincipleDecodeEncodeBHist integral,
        argumentPrincipleDecodeEncodeBHist residue,
        argumentPrincipleDecodeEncodeBHist reparam,
        argumentPrincipleDecodeEncodeBHist transport,
        argumentPrincipleDecodeEncodeBHist replay,
        argumentPrincipleDecodeEncodeBHist provenance,
        argumentPrincipleDecodeEncodeBHist name]

theorem argumentPrincipleToEventFlow_injective {x y : ArgumentPrincipleUp} :
    argumentPrincipleToEventFlow x = argumentPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : some x = some y := by
    calc
      some x = argumentPrincipleFromEventFlow (argumentPrincipleToEventFlow x) :=
        (argumentPrincipleRoundTrip x).symm
      _ = argumentPrincipleFromEventFlow (argumentPrincipleToEventFlow y) :=
        congrArg argumentPrincipleFromEventFlow heq
      _ = some y := argumentPrincipleRoundTrip y
  exact Option.some.inj hread

instance argumentPrincipleBHistCarrier : BHistCarrier ArgumentPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := argumentPrincipleToEventFlow
  fromEventFlow := argumentPrincipleFromEventFlow

instance argumentPrincipleChapterTasteGate :
    ChapterTasteGate ArgumentPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := argumentPrincipleRoundTrip
  layer_separation := by
    intro x y hneq heq
    exact hneq (argumentPrincipleToEventFlow_injective heq)

instance argumentPrincipleFieldFaithful : FieldFaithful ArgumentPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := argumentPrincipleFields
  field_faithful := by
    intro x y h
    cases x with
    | mk contour1 holomorphic1 zeroLedger1 poleLedger1 winding1 integral1 residue1
        reparam1 transport1 replay1 provenance1 name1 =>
      cases y with
      | mk contour2 holomorphic2 zeroLedger2 poleLedger2 winding2 integral2 residue2
          reparam2 transport2 replay2 provenance2 name2 =>
        cases h
        rfl

instance argumentPrincipleNontrivial : Nontrivial ArgumentPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArgumentPrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArgumentPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hContour
        cases hContour⟩

theorem ArgumentPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist, argumentPrincipleDecodeBHist (argumentPrincipleEncodeBHist h) = h) ∧
      (∀ x : ArgumentPrincipleUp,
        argumentPrincipleFromEventFlow (argumentPrincipleToEventFlow x) = some x) ∧
        (∀ x y : ArgumentPrincipleUp,
          argumentPrincipleToEventFlow x = argumentPrincipleToEventFlow y → x = y) ∧
          argumentPrincipleEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : ArgumentPrincipleUp,
              argumentPrincipleFields x = argumentPrincipleFields y → x = y) ∧
              (∃ x y : ArgumentPrincipleUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨argumentPrincipleDecodeEncodeBHist,
      argumentPrincipleRoundTrip,
      (fun _ _ heq => argumentPrincipleToEventFlow_injective heq),
      rfl,
      FieldFaithful.field_faithful,
      ⟨ArgumentPrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        ArgumentPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          injection h with hContour
          cases hContour⟩⟩

end BEDC.Derived.ArgumentPrincipleUp
