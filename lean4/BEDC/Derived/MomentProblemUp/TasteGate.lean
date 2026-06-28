import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MomentProblemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MomentProblemUp : Type where
  | mk
      (rat real hankel0 hankel1 window positivity distribution transport replay provenance
        localName : BHist) : MomentProblemUp
  deriving DecidableEq

def momentProblemFields : MomentProblemUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MomentProblemUp.mk rat real hankel0 hankel1 window positivity distribution transport replay
      provenance localName =>
      [rat, real, hankel0, hankel1, window, positivity, distribution, transport, replay,
        provenance, localName]

def momentProblemEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: momentProblemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: momentProblemEncodeBHist h

def momentProblemDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (momentProblemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (momentProblemDecodeBHist tail)

private theorem MomentProblemTasteGate_single_carrier_alignment_decode :
    forall h : BHist, momentProblemDecodeBHist (momentProblemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def momentProblemToEventFlow : MomentProblemUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MomentProblemUp.mk rat real hankel0 hankel1 window positivity distribution transport replay
      provenance localName =>
      [momentProblemEncodeBHist rat,
        momentProblemEncodeBHist real,
        momentProblemEncodeBHist hankel0,
        momentProblemEncodeBHist hankel1,
        momentProblemEncodeBHist window,
        momentProblemEncodeBHist positivity,
        momentProblemEncodeBHist distribution,
        momentProblemEncodeBHist transport,
        momentProblemEncodeBHist replay,
        momentProblemEncodeBHist provenance,
        momentProblemEncodeBHist localName]

def momentProblemFromEventFlow : EventFlow -> Option MomentProblemUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | rat :: rest0 =>
      match rest0 with
      | [] => none
      | real :: rest1 =>
          match rest1 with
          | [] => none
          | hankel0 :: rest2 =>
              match rest2 with
              | [] => none
              | hankel1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | window :: rest4 =>
                      match rest4 with
                      | [] => none
                      | positivity :: rest5 =>
                          match rest5 with
                          | [] => none
                          | distribution :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (MomentProblemUp.mk
                                                      (momentProblemDecodeBHist rat)
                                                      (momentProblemDecodeBHist real)
                                                      (momentProblemDecodeBHist hankel0)
                                                      (momentProblemDecodeBHist hankel1)
                                                      (momentProblemDecodeBHist window)
                                                      (momentProblemDecodeBHist positivity)
                                                      (momentProblemDecodeBHist distribution)
                                                      (momentProblemDecodeBHist transport)
                                                      (momentProblemDecodeBHist replay)
                                                      (momentProblemDecodeBHist provenance)
                                                      (momentProblemDecodeBHist localName))
                                              | _ :: _ => none

private theorem MomentProblemTasteGate_single_carrier_alignment_round_trip :
    forall x : MomentProblemUp, momentProblemFromEventFlow (momentProblemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rat real hankel0 hankel1 window positivity distribution transport replay provenance
      localName =>
      change
        some
          (MomentProblemUp.mk
            (momentProblemDecodeBHist (momentProblemEncodeBHist rat))
            (momentProblemDecodeBHist (momentProblemEncodeBHist real))
            (momentProblemDecodeBHist (momentProblemEncodeBHist hankel0))
            (momentProblemDecodeBHist (momentProblemEncodeBHist hankel1))
            (momentProblemDecodeBHist (momentProblemEncodeBHist window))
            (momentProblemDecodeBHist (momentProblemEncodeBHist positivity))
            (momentProblemDecodeBHist (momentProblemEncodeBHist distribution))
            (momentProblemDecodeBHist (momentProblemEncodeBHist transport))
            (momentProblemDecodeBHist (momentProblemEncodeBHist replay))
            (momentProblemDecodeBHist (momentProblemEncodeBHist provenance))
            (momentProblemDecodeBHist (momentProblemEncodeBHist localName))) =
          some
            (MomentProblemUp.mk rat real hankel0 hankel1 window positivity distribution
              transport replay provenance localName)
      rw [MomentProblemTasteGate_single_carrier_alignment_decode rat,
        MomentProblemTasteGate_single_carrier_alignment_decode real,
        MomentProblemTasteGate_single_carrier_alignment_decode hankel0,
        MomentProblemTasteGate_single_carrier_alignment_decode hankel1,
        MomentProblemTasteGate_single_carrier_alignment_decode window,
        MomentProblemTasteGate_single_carrier_alignment_decode positivity,
        MomentProblemTasteGate_single_carrier_alignment_decode distribution,
        MomentProblemTasteGate_single_carrier_alignment_decode transport,
        MomentProblemTasteGate_single_carrier_alignment_decode replay,
        MomentProblemTasteGate_single_carrier_alignment_decode provenance,
        MomentProblemTasteGate_single_carrier_alignment_decode localName]

private theorem MomentProblemTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MomentProblemUp} :
    momentProblemToEventFlow x = momentProblemToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      momentProblemFromEventFlow (momentProblemToEventFlow x) =
        momentProblemFromEventFlow (momentProblemToEventFlow y) :=
    congrArg momentProblemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MomentProblemTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MomentProblemTasteGate_single_carrier_alignment_round_trip y)))

instance momentProblemBHistCarrier : BHistCarrier MomentProblemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := momentProblemToEventFlow
  fromEventFlow := momentProblemFromEventFlow

instance momentProblemChapterTasteGate : ChapterTasteGate MomentProblemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change momentProblemFromEventFlow (momentProblemToEventFlow x) = some x
    exact MomentProblemTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MomentProblemTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def MomentProblemCarrier [AskSetup] [PackageSetup]
    (rat real hankel0 hankel1 window positivity distribution transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory rat ∧ UnaryHistory real ∧ UnaryHistory hankel0 ∧ UnaryHistory hankel1 ∧
    UnaryHistory window ∧ UnaryHistory positivity ∧ UnaryHistory distribution ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont rat real hankel0 ∧ Cont hankel0 hankel1 window ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace TasteGate

theorem MomentProblemTasteGate_single_carrier_alignment
    {rat real hankel0 hankel1 window positivity distribution transport replay provenance
      localName : BHist} :
    Cont rat real hankel0 ->
      momentProblemFields
          (MomentProblemUp.mk rat real hankel0 hankel1 window positivity distribution
            transport replay provenance localName) =
        [rat, real, hankel0, hankel1, window, positivity, distribution, transport, replay,
          provenance, localName] ∧
        Nonempty (BHistCarrier MomentProblemUp) ∧
          Nonempty (ChapterTasteGate MomentProblemUp) := by
  -- BEDC touchpoint anchor: BHist BMark Cont BHistCarrier ChapterTasteGate
  intro _ratReal
  exact ⟨rfl, ⟨momentProblemBHistCarrier⟩, ⟨momentProblemChapterTasteGate⟩⟩

end TasteGate

end BEDC.Derived.MomentProblemUp
