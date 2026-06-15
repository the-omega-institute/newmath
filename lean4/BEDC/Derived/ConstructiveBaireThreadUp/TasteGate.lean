import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveBaireThreadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveBaireThreadUp : Type where
  | mk (baire completeMetric stream regSeq realSeal specker transport replay localName :
      BHist) : ConstructiveBaireThreadUp
  deriving DecidableEq

def constructiveBaireThreadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveBaireThreadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveBaireThreadEncodeBHist h

def constructiveBaireThreadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveBaireThreadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveBaireThreadDecodeBHist tail)

private theorem constructiveBaireThread_decode_encode_bhist :
    ∀ h : BHist,
      constructiveBaireThreadDecodeBHist (constructiveBaireThreadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def constructiveBaireThreadFields : ConstructiveBaireThreadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveBaireThreadUp.mk baire completeMetric stream regSeq realSeal specker
      transport replay localName =>
      [baire, completeMetric, stream, regSeq, realSeal, specker, transport, replay,
        localName]

def constructiveBaireThreadToEventFlow : ConstructiveBaireThreadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map constructiveBaireThreadEncodeBHist (constructiveBaireThreadFields x)

def constructiveBaireThreadFromEventFlow : EventFlow → Option ConstructiveBaireThreadUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | baire :: rest0 =>
      match rest0 with
      | [] => none
      | completeMetric :: rest1 =>
          match rest1 with
          | [] => none
          | stream :: rest2 =>
              match rest2 with
              | [] => none
              | regSeq :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | specker :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ConstructiveBaireThreadUp.mk
                                              (constructiveBaireThreadDecodeBHist baire)
                                              (constructiveBaireThreadDecodeBHist
                                                completeMetric)
                                              (constructiveBaireThreadDecodeBHist stream)
                                              (constructiveBaireThreadDecodeBHist regSeq)
                                              (constructiveBaireThreadDecodeBHist
                                                realSeal)
                                              (constructiveBaireThreadDecodeBHist specker)
                                              (constructiveBaireThreadDecodeBHist
                                                transport)
                                              (constructiveBaireThreadDecodeBHist replay)
                                              (constructiveBaireThreadDecodeBHist
                                                localName))
                                      | _ :: _ => none

private theorem constructiveBaireThread_round_trip :
    ∀ x : ConstructiveBaireThreadUp,
      constructiveBaireThreadFromEventFlow (constructiveBaireThreadToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk baire completeMetric stream regSeq realSeal specker transport replay localName =>
      change
        some
          (ConstructiveBaireThreadUp.mk
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist baire))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist completeMetric))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist stream))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist regSeq))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist realSeal))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist specker))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist transport))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist replay))
            (constructiveBaireThreadDecodeBHist
              (constructiveBaireThreadEncodeBHist localName))) =
          some
            (ConstructiveBaireThreadUp.mk baire completeMetric stream regSeq realSeal
              specker transport replay localName)
      rw [constructiveBaireThread_decode_encode_bhist baire,
        constructiveBaireThread_decode_encode_bhist completeMetric,
        constructiveBaireThread_decode_encode_bhist stream,
        constructiveBaireThread_decode_encode_bhist regSeq,
        constructiveBaireThread_decode_encode_bhist realSeal,
        constructiveBaireThread_decode_encode_bhist specker,
        constructiveBaireThread_decode_encode_bhist transport,
        constructiveBaireThread_decode_encode_bhist replay,
        constructiveBaireThread_decode_encode_bhist localName]

private theorem constructiveBaireThreadToEventFlow_injective
    {x y : ConstructiveBaireThreadUp} :
    constructiveBaireThreadToEventFlow x = constructiveBaireThreadToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveBaireThreadFromEventFlow (constructiveBaireThreadToEventFlow x) =
        constructiveBaireThreadFromEventFlow (constructiveBaireThreadToEventFlow y) :=
    congrArg constructiveBaireThreadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (constructiveBaireThread_round_trip x).symm
      (Eq.trans hread (constructiveBaireThread_round_trip y)))

private theorem constructiveBaireThread_field_faithful :
    ∀ x y : ConstructiveBaireThreadUp,
      constructiveBaireThreadFields x = constructiveBaireThreadFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk baire₁ completeMetric₁ stream₁ regSeq₁ realSeal₁ specker₁ transport₁ replay₁
      localName₁ =>
      cases y with
      | mk baire₂ completeMetric₂ stream₂ regSeq₂ realSeal₂ specker₂ transport₂ replay₂
          localName₂ =>
          cases hfields
          rfl

instance constructiveBaireThreadBHistCarrier :
    BHistCarrier ConstructiveBaireThreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveBaireThreadToEventFlow
  fromEventFlow := constructiveBaireThreadFromEventFlow

instance constructiveBaireThreadChapterTasteGate :
    ChapterTasteGate ConstructiveBaireThreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveBaireThreadFromEventFlow (constructiveBaireThreadToEventFlow x) =
      some x
    exact constructiveBaireThread_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveBaireThreadToEventFlow_injective heq)

instance constructiveBaireThreadFieldFaithful :
    FieldFaithful ConstructiveBaireThreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveBaireThreadFields
  field_faithful := constructiveBaireThread_field_faithful

instance constructiveBaireThreadNontrivial :
    Nontrivial ConstructiveBaireThreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstructiveBaireThreadUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConstructiveBaireThreadUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConstructiveBaireThreadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveBaireThreadChapterTasteGate

def ConstructiveBaireThreadCarrier [AskSetup] [PackageSetup]
    (B K S R E P H C N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig
  Cont B K S ∧ Cont S R E ∧ Cont E P H ∧ Cont H C N ∧ PkgSig bundle N pkg

theorem ConstructiveBaireThreadCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B K S R E P H C N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConstructiveBaireThreadCarrier B K S R E P H C N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ConstructiveBaireThreadCarrier B K S R E P H C N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          ConstructiveBaireThreadCarrier B K S R E P H C N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          ConstructiveBaireThreadCarrier B K S R E P H C N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro N (And.intro packet (hsame_refl N))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.ConstructiveBaireThreadUp
