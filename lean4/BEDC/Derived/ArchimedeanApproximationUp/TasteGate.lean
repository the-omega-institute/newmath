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

namespace BEDC.Derived.ArchimedeanApproximationUp

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

inductive ArchimedeanApproximationUp : Type where
  | mk (N Q D epsilon S R E H C P M : BHist) : ArchimedeanApproximationUp
  deriving DecidableEq

def archimedeanApproximationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanApproximationEncodeBHist h

def archimedeanApproximationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanApproximationDecodeBHist tail)

private theorem ArchimedeanApproximationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanApproximationToEventFlow : ArchimedeanApproximationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanApproximationUp.mk N Q D epsilon S R E H C P M =>
      [archimedeanApproximationEncodeBHist N,
        archimedeanApproximationEncodeBHist Q,
        archimedeanApproximationEncodeBHist D,
        archimedeanApproximationEncodeBHist epsilon,
        archimedeanApproximationEncodeBHist S,
        archimedeanApproximationEncodeBHist R,
        archimedeanApproximationEncodeBHist E,
        archimedeanApproximationEncodeBHist H,
        archimedeanApproximationEncodeBHist C,
        archimedeanApproximationEncodeBHist P,
        archimedeanApproximationEncodeBHist M]

def archimedeanApproximationFromEventFlow : EventFlow -> Option ArchimedeanApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | N :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | epsilon :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | M :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ArchimedeanApproximationUp.mk
                                                      (archimedeanApproximationDecodeBHist N)
                                                      (archimedeanApproximationDecodeBHist Q)
                                                      (archimedeanApproximationDecodeBHist D)
                                                      (archimedeanApproximationDecodeBHist epsilon)
                                                      (archimedeanApproximationDecodeBHist S)
                                                      (archimedeanApproximationDecodeBHist R)
                                                      (archimedeanApproximationDecodeBHist E)
                                                      (archimedeanApproximationDecodeBHist H)
                                                      (archimedeanApproximationDecodeBHist C)
                                                      (archimedeanApproximationDecodeBHist P)
                                                      (archimedeanApproximationDecodeBHist M))
                                              | _ :: _ => none

private theorem ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip :
    forall x : ArchimedeanApproximationUp,
      archimedeanApproximationFromEventFlow
        (archimedeanApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N Q D epsilon S R E H C P M =>
      change
        some
          (ArchimedeanApproximationUp.mk
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist N))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist Q))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist D))
            (archimedeanApproximationDecodeBHist
              (archimedeanApproximationEncodeBHist epsilon))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist S))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist R))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist E))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist H))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist C))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist P))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist M))) =
          some (ArchimedeanApproximationUp.mk N Q D epsilon S R E H C P M)
      rw [ArchimedeanApproximationTasteGate_single_carrier_alignment_decode N,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode Q,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode D,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode epsilon,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode S,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode R,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode E,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode H,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode C,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode P,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode M]

private theorem ArchimedeanApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArchimedeanApproximationUp} :
    archimedeanApproximationToEventFlow x =
        archimedeanApproximationToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanApproximationFromEventFlow (archimedeanApproximationToEventFlow x) =
        archimedeanApproximationFromEventFlow (archimedeanApproximationToEventFlow y) :=
    congrArg archimedeanApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance archimedeanApproximationBHistCarrier :
    BHistCarrier ArchimedeanApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanApproximationToEventFlow
  fromEventFlow := archimedeanApproximationFromEventFlow

instance archimedeanApproximationChapterTasteGate :
    ChapterTasteGate ArchimedeanApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanApproximationFromEventFlow
        (archimedeanApproximationToEventFlow x) = some x
    exact ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ArchimedeanApproximationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist h) = h) /\
      Nonempty (BHistCarrier ArchimedeanApproximationUp) /\
        Nonempty (ChapterTasteGate ArchimedeanApproximationUp) /\
          archimedeanApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ArchimedeanApproximationTasteGate_single_carrier_alignment_decode,
      ⟨archimedeanApproximationBHistCarrier⟩,
      ⟨archimedeanApproximationChapterTasteGate⟩,
      rfl⟩

def ArchimedeanApproximationCarrier [AskSetup] [PackageSetup]
    (bound rational dyadic tolerance window readback sealRow transportRow replayRow
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory bound ∧ UnaryHistory rational ∧ UnaryHistory dyadic ∧
    UnaryHistory tolerance ∧ UnaryHistory window ∧ UnaryHistory readback ∧
      UnaryHistory sealRow ∧ UnaryHistory transportRow ∧ UnaryHistory replayRow ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont bound dyadic tolerance ∧ Cont tolerance window readback ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem ArchimedeanApproximationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg →
      Cont bound dyadic tolerance →
        Cont tolerance window readback →
          Cont readback sealRow realRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
                        hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                          hsame row sealRow ∨ hsame row realRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont bound dyadic tolerance ∧
                        Cont tolerance window readback ∧ Cont readback sealRow realRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier boundDyadic toleranceWindow readbackSeal provenancePkg namePkg
  obtain ⟨boundUnary, _rationalUnary, dyadicUnary, _toleranceUnary, windowUnary,
    _readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed boundUnary dyadicUnary boundDyadic
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary windowUnary toleranceWindow
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row rational ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row window ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bound dyadic tolerance ∧
              Cont tolerance window readback ∧ Cont readback sealRow realRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundDyadic, toleranceWindow, readbackSeal, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, realReadUnary⟩

theorem ArchimedeanApproximationCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {bound rational dyadic tolerance window readback sealRow transportRow replayRow provenance
      localName realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanApproximationCarrier bound rational dyadic tolerance window readback sealRow
        transportRow replayRow provenance localName bundle pkg →
      Cont bound dyadic tolerance →
        Cont tolerance window readback →
          Cont readback sealRow realRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                UnaryHistory realRead ∧ Cont bound dyadic tolerance ∧
                  Cont tolerance window readback ∧ Cont readback sealRow realRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier boundDyadic toleranceWindow readbackSeal provenancePkg namePkg
  obtain ⟨boundUnary, _rationalUnary, dyadicUnary, _toleranceUnary, windowUnary,
    _readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierBoundDyadic, _carrierToleranceWindow,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed boundUnary dyadicUnary boundDyadic
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary windowUnary toleranceWindow
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  exact
    ⟨realReadUnary, boundDyadic, toleranceWindow, readbackSeal, provenancePkg, namePkg⟩

end BEDC.Derived.ArchimedeanApproximationUp
