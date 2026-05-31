import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteNetEquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteNetEquicontinuityUp [AskSetup] : Type where
  | mk
      (compactNet family bounds tolerance modulus output transport replay provenance
        name : BHist)
      (centers : ProbeBundle ProbeName) :
      FiniteNetEquicontinuityUp

def finiteNetEquicontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteNetEquicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteNetEquicontinuityEncodeBHist h

def finiteNetEquicontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteNetEquicontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteNetEquicontinuityDecodeBHist tail)

private theorem finiteNetEquicontinuity_decode_encode_bhist :
    ∀ h : BHist,
      finiteNetEquicontinuityDecodeBHist
        (finiteNetEquicontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteNetEquicontinuityEncodeBundle [AskSetup] :
    ProbeBundle ProbeName → RawEvent
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | ProbeBundle.Bnil => []
  | ProbeBundle.Bcons _ tail =>
      BMark.b1 :: finiteNetEquicontinuityEncodeBundle tail

def finiteNetEquicontinuityRows [AskSetup] :
    FiniteNetEquicontinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteNetEquicontinuityUp.mk compactNet family bounds tolerance modulus output
      transport replay provenance name _centers =>
      [compactNet, family, bounds, tolerance, modulus, output, transport, replay,
        provenance, name]

def finiteNetEquicontinuityToEventFlow [AskSetup] :
    FiniteNetEquicontinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | x =>
      match x with
      | FiniteNetEquicontinuityUp.mk compactNet family bounds tolerance modulus output
          transport replay provenance name centers =>
          [finiteNetEquicontinuityEncodeBHist compactNet,
            finiteNetEquicontinuityEncodeBHist family,
            finiteNetEquicontinuityEncodeBHist bounds,
            finiteNetEquicontinuityEncodeBHist tolerance,
            finiteNetEquicontinuityEncodeBHist modulus,
            finiteNetEquicontinuityEncodeBHist output,
            finiteNetEquicontinuityEncodeBHist transport,
            finiteNetEquicontinuityEncodeBHist replay,
            finiteNetEquicontinuityEncodeBHist provenance,
            finiteNetEquicontinuityEncodeBHist name,
            finiteNetEquicontinuityEncodeBundle centers]

theorem FiniteNetEquicontinuityCarrier_rows_alignment [AskSetup] :
    (∀ h : BHist,
      finiteNetEquicontinuityDecodeBHist
        (finiteNetEquicontinuityEncodeBHist h) = h) ∧
      (∀ x : FiniteNetEquicontinuityUp,
        (finiteNetEquicontinuityRows x).map finiteNetEquicontinuityEncodeBHist =
          (finiteNetEquicontinuityToEventFlow x).take 10) ∧
        finiteNetEquicontinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  exact
    ⟨finiteNetEquicontinuity_decode_encode_bhist,
      (by
        intro x
        cases x with
        | mk compactNet family bounds tolerance modulus output transport replay provenance name
            centers =>
            rfl),
      rfl⟩

end BEDC.Derived.FiniteNetEquicontinuityUp
