import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricClosureUp

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

inductive MetricClosureUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (M T S L U W R E H C P N : BHist) : MetricClosureUp
  deriving DecidableEq

def metricClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricClosureEncodeBHist h

def metricClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricClosureDecodeBHist tail)

private theorem metricClosure_decode_encode_bhist :
    ∀ h : BHist,
      metricClosureDecodeBHist (metricClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricClosureToEventFlow : MetricClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricClosureUp.mk M T S L U W R E H C P N =>
      [metricClosureEncodeBHist M,
        metricClosureEncodeBHist T,
        metricClosureEncodeBHist S,
        metricClosureEncodeBHist L,
        metricClosureEncodeBHist U,
        metricClosureEncodeBHist W,
        metricClosureEncodeBHist R,
        metricClosureEncodeBHist E,
        metricClosureEncodeBHist H,
        metricClosureEncodeBHist C,
        metricClosureEncodeBHist P,
        metricClosureEncodeBHist N]

private def metricClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricClosureEventAtDefault index rest

def metricClosureFromEventFlow
    (ef : EventFlow) : Option MetricClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricClosureUp.mk
      (metricClosureDecodeBHist (metricClosureEventAtDefault 0 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 1 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 2 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 3 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 4 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 5 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 6 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 7 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 8 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 9 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 10 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 11 ef)))

private theorem metricClosure_round_trip :
    ∀ x : MetricClosureUp,
      metricClosureFromEventFlow (metricClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T S L U W R E H C P N =>
      change
        some
            (MetricClosureUp.mk
              (metricClosureDecodeBHist (metricClosureEncodeBHist M))
              (metricClosureDecodeBHist (metricClosureEncodeBHist T))
              (metricClosureDecodeBHist (metricClosureEncodeBHist S))
              (metricClosureDecodeBHist (metricClosureEncodeBHist L))
              (metricClosureDecodeBHist (metricClosureEncodeBHist U))
              (metricClosureDecodeBHist (metricClosureEncodeBHist W))
              (metricClosureDecodeBHist (metricClosureEncodeBHist R))
              (metricClosureDecodeBHist (metricClosureEncodeBHist E))
              (metricClosureDecodeBHist (metricClosureEncodeBHist H))
              (metricClosureDecodeBHist (metricClosureEncodeBHist C))
              (metricClosureDecodeBHist (metricClosureEncodeBHist P))
              (metricClosureDecodeBHist (metricClosureEncodeBHist N))) =
          some (MetricClosureUp.mk M T S L U W R E H C P N)
      rw [metricClosure_decode_encode_bhist M,
        metricClosure_decode_encode_bhist T,
        metricClosure_decode_encode_bhist S,
        metricClosure_decode_encode_bhist L,
        metricClosure_decode_encode_bhist U,
        metricClosure_decode_encode_bhist W,
        metricClosure_decode_encode_bhist R,
        metricClosure_decode_encode_bhist E,
        metricClosure_decode_encode_bhist H,
        metricClosure_decode_encode_bhist C,
        metricClosure_decode_encode_bhist P,
        metricClosure_decode_encode_bhist N]

private theorem metricClosureToEventFlow_injective
    {x y : MetricClosureUp} :
    metricClosureToEventFlow x = metricClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricClosureFromEventFlow (metricClosureToEventFlow x) =
        metricClosureFromEventFlow (metricClosureToEventFlow y) :=
    congrArg metricClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricClosure_round_trip x).symm
      (Eq.trans hread (metricClosure_round_trip y)))

def metricClosureFields : MetricClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricClosureUp.mk M T S L U W R E H C P N => [M, T, S, L, U, W, R, E, H, C, P, N]

private theorem metricClosure_fields_faithful :
    ∀ x y : MetricClosureUp,
      metricClosureFields x = metricClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M T S L U W R E H C P N =>
      cases y with
      | mk M' T' S' L' U' W' R' E' H' C' P' N' =>
          simp only [metricClosureFields] at h
          cases h
          rfl

instance metricClosureBHistCarrier : BHistCarrier MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricClosureToEventFlow
  fromEventFlow := metricClosureFromEventFlow

instance metricClosureChapterTasteGate : ChapterTasteGate MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricClosureFromEventFlow (metricClosureToEventFlow x) = some x
    exact metricClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricClosureToEventFlow_injective heq)

instance metricClosureFieldFaithful : FieldFaithful MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricClosureFields
  field_faithful := metricClosure_fields_faithful

instance metricClosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricClosureChapterTasteGate

theorem MetricClosureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricClosureUp) ∧
      Nonempty (FieldFaithful MetricClosureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetricClosureUp) ∧
          (∀ h : BHist,
            metricClosureDecodeBHist (metricClosureEncodeBHist h) = h) ∧
            (∀ x : MetricClosureUp,
              metricClosureFromEventFlow (metricClosureToEventFlow x) =
                some x) ∧
              (∀ x y : MetricClosureUp,
                metricClosureToEventFlow x = metricClosureToEventFlow y →
                  x = y) ∧
                metricClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨metricClosureChapterTasteGate⟩,
      ⟨metricClosureFieldFaithful⟩,
      ⟨metricClosureNontrivial⟩,
      metricClosure_decode_encode_bhist,
      metricClosure_round_trip,
      (fun _ _ heq => metricClosureToEventFlow_injective heq),
      rfl⟩

theorem MetricClosureCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M T S L U W R E H C P N neighborhoodRead metricRead windowRead readbackRead
      sealRead transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory T ->
        UnaryHistory S ->
          UnaryHistory L ->
            UnaryHistory U ->
              UnaryHistory W ->
                UnaryHistory R ->
                  UnaryHistory E ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory P ->
                          UnaryHistory N ->
                            Cont M T neighborhoodRead ->
                              Cont neighborhoodRead U metricRead ->
                                Cont metricRead W windowRead ->
                                  Cont windowRead R readbackRead ->
                                    Cont readbackRead E sealRead ->
                                      Cont sealRead H transportRead ->
                                        Cont transportRead C replayRead ->
                                          Cont P N namedRead ->
                                            PkgSig bundle P pkg ->
                                              PkgSig bundle N pkg ->
                                                PkgSig bundle namedRead pkg ->
                                                  SemanticNameCert
                                                      (fun row : BHist =>
                                                        hsame row namedRead ∧
                                                          UnaryHistory row)
                                                      (fun row : BHist =>
                                                        hsame row M ∨ hsame row T ∨
                                                          hsame row S ∨ hsame row L ∨
                                                            hsame row U ∨ hsame row W ∨
                                                              hsame row R ∨ hsame row E ∨
                                                                hsame row H ∨
                                                                  hsame row C ∨
                                                                    hsame row P ∨
                                                                      hsame row N ∨
                                                                        hsame row namedRead)
                                                      (fun row : BHist =>
                                                        UnaryHistory row ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg ∧
                                                              PkgSig bundle namedRead pkg)
                                                      hsame ∧ UnaryHistory neighborhoodRead ∧
                                                    UnaryHistory metricRead ∧
                                                  UnaryHistory windowRead ∧
                                                UnaryHistory readbackRead ∧
                                              UnaryHistory sealRead ∧
                                            UnaryHistory transportRead ∧
                                          UnaryHistory replayRead ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro mUnary tUnary _sUnary _lUnary uUnary wUnary rUnary eUnary hUnary cUnary pUnary
    nUnary neighborhoodRoute metricRoute windowRoute readbackRoute sealRoute transportRoute
    replayRoute namedRoute pkgP pkgN pkgNamed
  have neighborhoodUnary : UnaryHistory neighborhoodRead :=
    unary_cont_closed mUnary tUnary neighborhoodRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed neighborhoodUnary uUnary metricRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed metricUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row S ∨ hsame row L ∨ hsame row U ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP, pkgN, pkgNamed⟩
  }
  exact
    ⟨cert, neighborhoodUnary, metricUnary, windowUnary, readbackUnary, sealUnary,
      transportUnary, replayUnary, namedUnary⟩

end BEDC.Derived.MetricClosureUp
