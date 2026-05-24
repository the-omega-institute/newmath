import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived

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

def SecondCountableUp [AskSetup] [PackageSetup]
    (source topology metric base dyadic stream realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory topology ∧ UnaryHistory metric ∧ UnaryHistory base ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source base replay ∧ Cont metric dyadic stream ∧
          Cont stream topology realSeal ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived

namespace BEDC.Derived.SecondCountableUp

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

inductive SecondCountableUp : Type where
  | mk (X T M B D S R H C P N : BHist) : SecondCountableUp
  deriving DecidableEq

def secondCountableEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: secondCountableEncodeBHist h
  | BHist.e1 h => BMark.b1 :: secondCountableEncodeBHist h

def secondCountableDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (secondCountableDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (secondCountableDecodeBHist tail)

private theorem secondCountableDecodeEncode :
    ∀ h : BHist, secondCountableDecodeBHist (secondCountableEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def secondCountableFields : SecondCountableUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SecondCountableUp.mk X T M B D S R H C P N => [X, T, M, B, D, S, R, H, C, P, N]

def secondCountableToEventFlow : SecondCountableUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (secondCountableFields x).map secondCountableEncodeBHist

private def secondCountableEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => secondCountableEventAt index rest

def secondCountableFromEventFlow (ef : EventFlow) : Option SecondCountableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SecondCountableUp.mk
      (secondCountableDecodeBHist (secondCountableEventAt 0 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 1 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 2 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 3 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 4 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 5 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 6 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 7 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 8 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 9 ef))
      (secondCountableDecodeBHist (secondCountableEventAt 10 ef)))

private theorem secondCountableRoundTrip (x : SecondCountableUp) :
    secondCountableFromEventFlow (secondCountableToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X T M B D S R H C P N =>
      change
        some
          (SecondCountableUp.mk
            (secondCountableDecodeBHist (secondCountableEncodeBHist X))
            (secondCountableDecodeBHist (secondCountableEncodeBHist T))
            (secondCountableDecodeBHist (secondCountableEncodeBHist M))
            (secondCountableDecodeBHist (secondCountableEncodeBHist B))
            (secondCountableDecodeBHist (secondCountableEncodeBHist D))
            (secondCountableDecodeBHist (secondCountableEncodeBHist S))
            (secondCountableDecodeBHist (secondCountableEncodeBHist R))
            (secondCountableDecodeBHist (secondCountableEncodeBHist H))
            (secondCountableDecodeBHist (secondCountableEncodeBHist C))
            (secondCountableDecodeBHist (secondCountableEncodeBHist P))
            (secondCountableDecodeBHist (secondCountableEncodeBHist N))) =
          some (SecondCountableUp.mk X T M B D S R H C P N)
      rw [secondCountableDecodeEncode X,
        secondCountableDecodeEncode T,
        secondCountableDecodeEncode M,
        secondCountableDecodeEncode B,
        secondCountableDecodeEncode D,
        secondCountableDecodeEncode S,
        secondCountableDecodeEncode R,
        secondCountableDecodeEncode H,
        secondCountableDecodeEncode C,
        secondCountableDecodeEncode P,
        secondCountableDecodeEncode N]

private theorem secondCountableToEventFlow_injective
    {x y : SecondCountableUp} :
    secondCountableToEventFlow x = secondCountableToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      secondCountableFromEventFlow (secondCountableToEventFlow x) =
        secondCountableFromEventFlow (secondCountableToEventFlow y) :=
    congrArg secondCountableFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (secondCountableRoundTrip x).symm
      (Eq.trans hread (secondCountableRoundTrip y)))

instance secondCountableBHistCarrier : BHistCarrier SecondCountableUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := secondCountableToEventFlow
  fromEventFlow := secondCountableFromEventFlow

instance secondCountableChapterTasteGate : ChapterTasteGate SecondCountableUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change secondCountableFromEventFlow (secondCountableToEventFlow x) = some x
    exact secondCountableRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (secondCountableToEventFlow_injective heq)

private theorem secondCountableFields_faithful :
    ∀ x y : SecondCountableUp, secondCountableFields x = secondCountableFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ T₁ M₁ B₁ D₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ T₂ M₂ B₂ D₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance secondCountableFieldFaithful : FieldFaithful SecondCountableUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := secondCountableFields
  field_faithful := secondCountableFields_faithful

instance secondCountableNontrivial : Nontrivial SecondCountableUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SecondCountableUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SecondCountableUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SecondCountableTasteGate_single_carrier_alignment :
    (∀ h : BHist, secondCountableDecodeBHist (secondCountableEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SecondCountableUp) ∧ Nonempty (ChapterTasteGate SecondCountableUp) ∧
        secondCountableEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨secondCountableDecodeEncode,
      ⟨⟨secondCountableBHistCarrier⟩, ⟨secondCountableChapterTasteGate⟩, rfl⟩⟩

theorem SecondCountableCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source topology metric base dyadic stream realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.SecondCountableUp source topology metric base dyadic stream realSeal transport
        replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BEDC.Derived.SecondCountableUp source topology metric base dyadic stream realSeal
            transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.SecondCountableUp source topology metric base dyadic stream realSeal
            transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.SecondCountableUp source topology metric base dyadic stream realSeal
            transport replay provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  constructor
  · constructor
    · exact Exists.intro localName (And.intro carrier (hsame_refl localName))
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameRow sameRow'
      exact hsame_trans sameRow sameRow'
    · intro row row' sameRows sourceRow
      exact And.intro carrier (hsame_trans (hsame_symm sameRows) sourceRow.right)
  · intro _row source
    exact source
  · intro _row source
    exact source

theorem SecondCountableCarrier_metric_base_handoff [AskSetup] [PackageSetup]
    {source topology metric base dyadic stream realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.SecondCountableUp source topology metric base dyadic stream realSeal transport
        replay provenance localName bundle pkg ->
      UnaryHistory metric ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
        UnaryHistory topology ∧ UnaryHistory realSeal ∧ Cont metric dyadic stream ∧
          Cont stream topology realSeal ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  cases carrier with
  | intro _sourceUnary restTopology =>
      cases restTopology with
      | intro topologyUnary restMetric =>
          cases restMetric with
          | intro metricUnary restBase =>
              cases restBase with
              | intro _baseUnary restDyadic =>
                  cases restDyadic with
                  | intro dyadicUnary restStream =>
                      cases restStream with
                      | intro streamUnary restRealSeal =>
                          cases restRealSeal with
                          | intro realSealUnary restTransport =>
                              cases restTransport with
                              | intro _transportUnary restReplay =>
                                  cases restReplay with
                                  | intro _replayUnary restProvenance =>
                                      cases restProvenance with
                                      | intro _provenanceUnary restLocalName =>
                                          cases restLocalName with
                                          | intro _localNameUnary restSourceBase =>
                                              cases restSourceBase with
                                              | intro _sourceBaseCont restMetricDyadic =>
                                                  cases restMetricDyadic with
                                                  | intro metricDyadicCont restStreamTopology =>
                                                      cases restStreamTopology with
                                                      | intro streamTopologyCont restTransportReplay =>
                                                          cases restTransportReplay with
                                                          | intro _transportReplayCont restPkg =>
                                                              cases restPkg with
                                                              | intro provenancePkg localNamePkg =>
                                                                  constructor
                                                                  · exact metricUnary
                                                                  · constructor
                                                                    · exact dyadicUnary
                                                                    · constructor
                                                                      · exact streamUnary
                                                                      · constructor
                                                                        · exact topologyUnary
                                                                        · constructor
                                                                          · exact realSealUnary
                                                                          · constructor
                                                                            · exact metricDyadicCont
                                                                            · constructor
                                                                              · exact streamTopologyCont
                                                                              · constructor
                                                                                · exact provenancePkg
                                                                                · exact localNamePkg

end BEDC.Derived.SecondCountableUp
