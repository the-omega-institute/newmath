import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanCauchyTailUp

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

inductive ArchimedeanCauchyTailUp : Type where
  | mk (real bound modulus equivalence window readback dyadic transport replay provenance
      name : BHist) : ArchimedeanCauchyTailUp
  deriving DecidableEq

def archimedeanCauchyTailEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanCauchyTailEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanCauchyTailEncodeBHist h

def archimedeanCauchyTailDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanCauchyTailDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanCauchyTailDecodeBHist tail)

private theorem archimedeanCauchyTail_decode_encode :
    ∀ h : BHist, archimedeanCauchyTailDecodeBHist
      (archimedeanCauchyTailEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanCauchyTailFields : ArchimedeanCauchyTailUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanCauchyTailUp.mk real bound modulus equivalence window readback dyadic
      transport replay provenance name =>
      [real, bound, modulus, equivalence, window, readback, dyadic, transport, replay,
        provenance, name]

def archimedeanCauchyTailToEventFlow : ArchimedeanCauchyTailUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map archimedeanCauchyTailEncodeBHist (archimedeanCauchyTailFields x)

def archimedeanCauchyTailFromEventFlow : EventFlow → Option ArchimedeanCauchyTailUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | real :: restReal =>
      match restReal with
      | [] => none
      | bound :: restBound =>
          match restBound with
          | [] => none
          | modulus :: restModulus =>
              match restModulus with
              | [] => none
              | equivalence :: restEquivalence =>
                  match restEquivalence with
                  | [] => none
                  | window :: restWindow =>
                      match restWindow with
                      | [] => none
                      | readback :: restReadback =>
                          match restReadback with
                          | [] => none
                          | dyadic :: restDyadic =>
                              match restDyadic with
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
                                                    (ArchimedeanCauchyTailUp.mk
                                                      (archimedeanCauchyTailDecodeBHist real)
                                                      (archimedeanCauchyTailDecodeBHist bound)
                                                      (archimedeanCauchyTailDecodeBHist modulus)
                                                      (archimedeanCauchyTailDecodeBHist
                                                        equivalence)
                                                      (archimedeanCauchyTailDecodeBHist window)
                                                      (archimedeanCauchyTailDecodeBHist readback)
                                                      (archimedeanCauchyTailDecodeBHist dyadic)
                                                      (archimedeanCauchyTailDecodeBHist
                                                        transport)
                                                      (archimedeanCauchyTailDecodeBHist replay)
                                                      (archimedeanCauchyTailDecodeBHist
                                                        provenance)
                                                      (archimedeanCauchyTailDecodeBHist name))
                                              | _ :: _ => none

private theorem archimedeanCauchyTail_round_trip :
    ∀ x : ArchimedeanCauchyTailUp,
      archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk real bound modulus equivalence window readback dyadic transport replay provenance name =>
      change
        some
          (ArchimedeanCauchyTailUp.mk
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist real))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist bound))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist modulus))
            (archimedeanCauchyTailDecodeBHist
              (archimedeanCauchyTailEncodeBHist equivalence))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist window))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist readback))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist dyadic))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist transport))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist replay))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist provenance))
            (archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist name))) =
          some
            (ArchimedeanCauchyTailUp.mk real bound modulus equivalence window readback dyadic
              transport replay provenance name)
      rw [archimedeanCauchyTail_decode_encode real,
        archimedeanCauchyTail_decode_encode bound,
        archimedeanCauchyTail_decode_encode modulus,
        archimedeanCauchyTail_decode_encode equivalence,
        archimedeanCauchyTail_decode_encode window,
        archimedeanCauchyTail_decode_encode readback,
        archimedeanCauchyTail_decode_encode dyadic,
        archimedeanCauchyTail_decode_encode transport,
        archimedeanCauchyTail_decode_encode replay,
        archimedeanCauchyTail_decode_encode provenance,
        archimedeanCauchyTail_decode_encode name]

private theorem archimedeanCauchyTailToEventFlow_injective
    {x y : ArchimedeanCauchyTailUp} :
    archimedeanCauchyTailToEventFlow x = archimedeanCauchyTailToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow x) =
        archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow y) :=
    congrArg archimedeanCauchyTailFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (archimedeanCauchyTail_round_trip x).symm
      (Eq.trans hread (archimedeanCauchyTail_round_trip y)))

private theorem archimedeanCauchyTail_fields_faithful :
    ∀ x y : ArchimedeanCauchyTailUp,
      archimedeanCauchyTailFields x = archimedeanCauchyTailFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk real₁ bound₁ modulus₁ equivalence₁ window₁ readback₁ dyadic₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk real₂ bound₂ modulus₂ equivalence₂ window₂ readback₂ dyadic₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance archimedeanCauchyTailBHistCarrier : BHistCarrier ArchimedeanCauchyTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanCauchyTailToEventFlow
  fromEventFlow := archimedeanCauchyTailFromEventFlow

instance archimedeanCauchyTailChapterTasteGate :
    ChapterTasteGate ArchimedeanCauchyTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanCauchyTailFromEventFlow (archimedeanCauchyTailToEventFlow x) = some x
    exact archimedeanCauchyTail_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanCauchyTailToEventFlow_injective heq)

instance archimedeanCauchyTailFieldFaithful : FieldFaithful ArchimedeanCauchyTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanCauchyTailFields
  field_faithful := archimedeanCauchyTail_fields_faithful

def taste_gate : ChapterTasteGate ArchimedeanCauchyTailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanCauchyTailChapterTasteGate

theorem ArchimedeanCauchyTailTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ArchimedeanCauchyTailUp) ∧
      Nonempty (ChapterTasteGate ArchimedeanCauchyTailUp) ∧
        (∀ h : BHist,
          archimedeanCauchyTailDecodeBHist (archimedeanCauchyTailEncodeBHist h) = h) ∧
          archimedeanCauchyTailEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨archimedeanCauchyTailBHistCarrier⟩,
      ⟨archimedeanCauchyTailChapterTasteGate⟩,
      archimedeanCauchyTail_decode_encode,
      rfl⟩

def ArchimedeanCauchyTailCarrier [AskSetup] [PackageSetup]
    (real bound modulus equivalence window readback dyadic transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory real ∧ UnaryHistory bound ∧ UnaryHistory modulus ∧
    UnaryHistory equivalence ∧ UnaryHistory window ∧ UnaryHistory readback ∧
      UnaryHistory dyadic ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ Cont real bound modulus ∧
          Cont modulus equivalence window ∧ Cont window readback dyadic ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem ArchimedeanCauchyTailCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {real bound modulus equivalence window readback dyadic transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanCauchyTailCarrier real bound modulus equivalence window readback dyadic
        transport replay provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ArchimedeanCauchyTailCarrier real bound modulus equivalence window readback dyadic
              transport replay provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          hsame row real ∨ hsame row bound ∨ hsame row modulus ∨ hsame row equivalence ∨
            hsame row window ∨ hsame row readback ∨ hsame row dyadic ∨
              hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                hsame row name)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierSource :
      ArchimedeanCauchyTailCarrier real bound modulus equivalence window readback dyadic
        transport replay provenance name bundle pkg := carrier
  obtain ⟨_realUnary, _boundUnary, _modulusUnary, _equivalenceUnary, _windowUnary,
    _readbackUnary, _dyadicUnary, _transportUnary, _replayUnary, _provenanceUnary,
    nameUnary, _boundRoute, _tailRoute, _dyadicRoute, _replayRoute, _provenancePkg,
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr source.right)))))))))
    ledger_sound := by
      intro row source
      cases source.right
      exact ⟨nameUnary, namePkg⟩
  }

end BEDC.Derived.ArchimedeanCauchyTailUp
