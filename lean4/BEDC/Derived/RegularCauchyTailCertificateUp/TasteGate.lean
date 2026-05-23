import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailCertificateUp

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

inductive RegularCauchyTailCertificateUp : Type where
  | mk
      (source window readback dyadic realSeal transports routes provenance name : BHist) :
      RegularCauchyTailCertificateUp
  deriving DecidableEq

def regularCauchyTailCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailCertificateEncodeBHist h

def regularCauchyTailCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailCertificateDecodeBHist tail)

private theorem regularCauchyTailCertificate_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailCertificateDecodeBHist
        (regularCauchyTailCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailCertificateToEventFlow :
    RegularCauchyTailCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailCertificateUp.mk source window readback dyadic realSeal transports routes
      provenance name =>
      [regularCauchyTailCertificateEncodeBHist source,
        regularCauchyTailCertificateEncodeBHist window,
        regularCauchyTailCertificateEncodeBHist readback,
        regularCauchyTailCertificateEncodeBHist dyadic,
        regularCauchyTailCertificateEncodeBHist realSeal,
        regularCauchyTailCertificateEncodeBHist transports,
        regularCauchyTailCertificateEncodeBHist routes,
        regularCauchyTailCertificateEncodeBHist provenance,
        regularCauchyTailCertificateEncodeBHist name]

def regularCauchyTailCertificateFromEventFlow :
    EventFlow → Option RegularCauchyTailCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [
      source,
      window,
      readback,
      dyadic,
      realSeal,
      transports,
      routes,
      provenance,
      name
    ] =>
      some
        (RegularCauchyTailCertificateUp.mk
          (regularCauchyTailCertificateDecodeBHist source)
          (regularCauchyTailCertificateDecodeBHist window)
          (regularCauchyTailCertificateDecodeBHist readback)
          (regularCauchyTailCertificateDecodeBHist dyadic)
          (regularCauchyTailCertificateDecodeBHist realSeal)
          (regularCauchyTailCertificateDecodeBHist transports)
          (regularCauchyTailCertificateDecodeBHist routes)
          (regularCauchyTailCertificateDecodeBHist provenance)
          (regularCauchyTailCertificateDecodeBHist name))
  | _ => none

private theorem regularCauchyTailCertificate_round_trip :
    ∀ x : RegularCauchyTailCertificateUp,
      regularCauchyTailCertificateFromEventFlow
        (regularCauchyTailCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source window readback dyadic realSeal transports routes provenance name =>
      change
        some
          (RegularCauchyTailCertificateUp.mk
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist source))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist window))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist readback))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist dyadic))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist realSeal))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist transports))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist routes))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist provenance))
            (regularCauchyTailCertificateDecodeBHist
              (regularCauchyTailCertificateEncodeBHist name))) =
          some
            (RegularCauchyTailCertificateUp.mk source window readback dyadic realSeal
              transports routes provenance name)
      rw [regularCauchyTailCertificate_decode_encode_bhist source,
        regularCauchyTailCertificate_decode_encode_bhist window,
        regularCauchyTailCertificate_decode_encode_bhist readback,
        regularCauchyTailCertificate_decode_encode_bhist dyadic,
        regularCauchyTailCertificate_decode_encode_bhist realSeal,
        regularCauchyTailCertificate_decode_encode_bhist transports,
        regularCauchyTailCertificate_decode_encode_bhist routes,
        regularCauchyTailCertificate_decode_encode_bhist provenance,
        regularCauchyTailCertificate_decode_encode_bhist name]

private theorem regularCauchyTailCertificateToEventFlow_injective
    {x y : RegularCauchyTailCertificateUp} :
    regularCauchyTailCertificateToEventFlow x =
      regularCauchyTailCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailCertificateFromEventFlow
          (regularCauchyTailCertificateToEventFlow x) =
        regularCauchyTailCertificateFromEventFlow
          (regularCauchyTailCertificateToEventFlow y) :=
    congrArg regularCauchyTailCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailCertificate_round_trip x).symm
      (Eq.trans hread (regularCauchyTailCertificate_round_trip y)))

def regularCauchyTailCertificateFields :
    RegularCauchyTailCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailCertificateUp.mk source window readback dyadic realSeal transports routes
      provenance name =>
      [source, window, readback, dyadic, realSeal, transports, routes, provenance, name]

private theorem regularCauchyTailCertificate_field_faithful :
    ∀ x y : RegularCauchyTailCertificateUp,
      regularCauchyTailCertificateFields x = regularCauchyTailCertificateFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ window₁ readback₁ dyadic₁ realSeal₁ transports₁ routes₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ window₂ readback₂ dyadic₂ realSeal₂ transports₂ routes₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance regularCauchyTailCertificateBHistCarrier :
    BHistCarrier RegularCauchyTailCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailCertificateToEventFlow
  fromEventFlow := regularCauchyTailCertificateFromEventFlow

instance regularCauchyTailCertificateChapterTasteGate :
    ChapterTasteGate RegularCauchyTailCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailCertificateFromEventFlow
        (regularCauchyTailCertificateToEventFlow x) = some x
    exact regularCauchyTailCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailCertificateToEventFlow_injective heq)

instance regularCauchyTailCertificateFieldFaithful :
    FieldFaithful RegularCauchyTailCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  fields := regularCauchyTailCertificateFields
  field_faithful := regularCauchyTailCertificate_field_faithful

instance regularCauchyTailCertificateNontrivial :
    Nontrivial RegularCauchyTailCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailCertificateUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailCertificateChapterTasteGate

theorem RegularCauchyTailCertificateNameCertObligations [AskSetup] [PackageSetup]
    {source window readback dyadic sealRow transport replay provenance localName windowRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory window ->
        UnaryHistory readback ->
          UnaryHistory dyadic ->
            UnaryHistory sealRow ->
              UnaryHistory replay ->
                UnaryHistory localName ->
                  Cont source window windowRead ->
                    Cont readback dyadic sealRead ->
                      Cont replay localName namedRead ->
                        PkgSig bundle namedRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row windowRead \/ hsame row sealRead \/
                                  hsame row namedRead)
                              (fun row : BHist => PkgSig bundle namedRead pkg /\
                                hsame row namedRead)
                              hsame /\
                            UnaryHistory windowRead /\ UnaryHistory sealRead /\
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro sourceUnary windowUnary readbackUnary dyadicUnary _sealUnary replayUnary localNameUnary
    sourceWindow readbackDyadic replayLocalName namedPkg
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadic
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary localNameUnary replayLocalName
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
        (fun row : BHist =>
          hsame row windowRead \/ hsame row sealRead \/ hsame row namedRead)
        (fun row : BHist => PkgSig bundle namedRead pkg /\ hsame row namedRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨namedPkg, source.left⟩
  }
  exact ⟨cert, windowReadUnary, sealReadUnary, namedReadUnary⟩

end BEDC.Derived.RegularCauchyTailCertificateUp
