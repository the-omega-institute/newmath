import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonoidalCompletionUp

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

inductive MonoidalCompletionUp : Type where
  | mk (metric unit counit product assoc symmetry transport replay provenance name : BHist) :
      MonoidalCompletionUp
  deriving DecidableEq

def monoidalCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monoidalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monoidalCompletionEncodeBHist h

def monoidalCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monoidalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monoidalCompletionDecodeBHist tail)

private theorem monoidalCompletion_decode_encode :
    ∀ h : BHist, monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monoidalCompletionFields : MonoidalCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonoidalCompletionUp.mk metric unit counit product assoc symmetry transport replay
      provenance name =>
      [metric, unit, counit, product, assoc, symmetry, transport, replay, provenance, name]

def monoidalCompletionToEventFlow : MonoidalCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map monoidalCompletionEncodeBHist (monoidalCompletionFields x)

def monoidalCompletionFromEventFlow : EventFlow → Option MonoidalCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | metric :: restMetric =>
      match restMetric with
      | [] => none
      | unit :: restUnit =>
          match restUnit with
          | [] => none
          | counit :: restCounit =>
              match restCounit with
              | [] => none
              | product :: restProduct =>
                  match restProduct with
                  | [] => none
                  | assoc :: restAssoc =>
                      match restAssoc with
                      | [] => none
                      | symmetry :: restSymmetry =>
                          match restSymmetry with
                          | [] => none
                          | transport :: restTransport =>
                              match restTransport with
                              | [] => none
                              | replay :: restReplay =>
                                  match restReplay with
                                  | [] => none
                                  | provenance :: restProvenance =>
                                      match restProvenance with
                                      | [] => none
                                      | name :: restName =>
                                          match restName with
                                          | [] =>
                                              some
                                                (MonoidalCompletionUp.mk
                                                  (monoidalCompletionDecodeBHist metric)
                                                  (monoidalCompletionDecodeBHist unit)
                                                  (monoidalCompletionDecodeBHist counit)
                                                  (monoidalCompletionDecodeBHist product)
                                                  (monoidalCompletionDecodeBHist assoc)
                                                  (monoidalCompletionDecodeBHist symmetry)
                                                  (monoidalCompletionDecodeBHist transport)
                                                  (monoidalCompletionDecodeBHist replay)
                                                  (monoidalCompletionDecodeBHist provenance)
                                                  (monoidalCompletionDecodeBHist name))
                                          | _ :: _ => none

private theorem monoidalCompletion_round_trip :
    ∀ x : MonoidalCompletionUp,
      monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric unit counit product assoc symmetry transport replay provenance name =>
      change
        some
          (MonoidalCompletionUp.mk
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist metric))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist unit))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist counit))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist product))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist assoc))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist symmetry))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist transport))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist replay))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist provenance))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist name))) =
          some
            (MonoidalCompletionUp.mk metric unit counit product assoc symmetry transport replay
              provenance name)
      rw [monoidalCompletion_decode_encode metric, monoidalCompletion_decode_encode unit,
        monoidalCompletion_decode_encode counit, monoidalCompletion_decode_encode product,
        monoidalCompletion_decode_encode assoc, monoidalCompletion_decode_encode symmetry,
        monoidalCompletion_decode_encode transport, monoidalCompletion_decode_encode replay,
        monoidalCompletion_decode_encode provenance, monoidalCompletion_decode_encode name]

private theorem monoidalCompletionToEventFlow_injective {x y : MonoidalCompletionUp} :
    monoidalCompletionToEventFlow x = monoidalCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) =
        monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow y) :=
    congrArg monoidalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monoidalCompletion_round_trip x).symm
      (Eq.trans hread (monoidalCompletion_round_trip y)))

instance monoidalCompletionBHistCarrier : BHistCarrier MonoidalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monoidalCompletionToEventFlow
  fromEventFlow := monoidalCompletionFromEventFlow

instance monoidalCompletionChapterTasteGate : ChapterTasteGate MonoidalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) = some x
    exact monoidalCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monoidalCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MonoidalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monoidalCompletionChapterTasteGate

def MonoidalCompletionCarrier [AskSetup] [PackageSetup]
    (metric unit counit product assoc symmetry transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory metric ∧ UnaryHistory unit ∧ UnaryHistory counit ∧ UnaryHistory product ∧
    UnaryHistory assoc ∧ UnaryHistory symmetry ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont metric unit counit ∧ Cont counit product assoc ∧
          Cont assoc symmetry transport ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem MonoidalCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric unit counit product assoc symmetry transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonoidalCompletionCarrier metric unit counit product assoc symmetry transport replay
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MonoidalCompletionCarrier metric unit counit product assoc symmetry transport replay
              provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          hsame row metric ∨ hsame row unit ∨ hsame row counit ∨ hsame row product ∨
            hsame row assoc ∨ hsame row symmetry ∨ hsame row transport ∨
              hsame row replay ∨ hsame row provenance ∨ hsame row name)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierSource :
      MonoidalCompletionCarrier metric unit counit product assoc symmetry transport replay
        provenance name bundle pkg := carrier
  obtain ⟨_metricUnary, _unitUnary, _counitUnary, _productUnary, _assocUnary,
    _symmetryUnary, _transportUnary, _replayUnary, _provenanceUnary, nameUnary,
    _reflectorRoute, _productRoute, _coherenceRoute, _replayRoute, _provenancePkg,
    namePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro name ⟨carrierSource, hsame_refl name⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))))))
    ledger_sound := by
      intro row source
      cases source.right
      exact ⟨nameUnary, namePkg⟩
  }

end BEDC.Derived.MonoidalCompletionUp
