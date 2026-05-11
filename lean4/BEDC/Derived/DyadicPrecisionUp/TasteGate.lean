import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicPrecisionUp

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

inductive DyadicPrecisionUp : Type where
  | mk (precision radius window hrow contRow provenance cert ledger : BHist) :
      DyadicPrecisionUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def DyadicPrecisionSchedule_namecert_obligations_toEventFlow : DyadicPrecisionUp → EventFlow
  | DyadicPrecisionUp.mk precision radius window hrow contRow provenance cert ledger =>
      [[BMark.b0], encodeBHist precision,
        [BMark.b1, BMark.b0], encodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist hrow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist contRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist cert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          encodeBHist ledger]

def DyadicPrecisionSchedule_namecert_obligations_fromEventFlow :
    EventFlow → Option DyadicPrecisionUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | precision :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | radius :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | hrow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | contRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | cert :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DyadicPrecisionUp.mk
                                                                          (decodeBHist precision)
                                                                          (decodeBHist radius)
                                                                          (decodeBHist window)
                                                                          (decodeBHist hrow)
                                                                          (decodeBHist contRow)
                                                                          (decodeBHist provenance)
                                                                          (decodeBHist cert)
                                                                          (decodeBHist ledger))
                                                                  | _ :: _ => none

theorem DyadicPrecisionSchedule_namecert_obligations_round_trip :
    ∀ x : DyadicPrecisionUp, DyadicPrecisionSchedule_namecert_obligations_fromEventFlow
      (DyadicPrecisionSchedule_namecert_obligations_toEventFlow x) = some x := by
  intro x
  cases x with
  | mk precision radius window hrow contRow provenance cert ledger =>
      change
        some (DyadicPrecisionUp.mk (decodeBHist (encodeBHist precision))
          (decodeBHist (encodeBHist radius)) (decodeBHist (encodeBHist window))
          (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
          (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
          (decodeBHist (encodeBHist ledger))) =
          some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance cert
            ledger)
      have hPrecision :
          some (DyadicPrecisionUp.mk (decodeBHist (encodeBHist precision))
            (decodeBHist (encodeBHist radius)) (decodeBHist (encodeBHist window))
            (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
            (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
            (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision (decodeBHist (encodeBHist radius))
              (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist hrow))
              (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk row (decodeBHist (encodeBHist radius))
              (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist hrow))
              (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist precision)
      have hRadius :
          some (DyadicPrecisionUp.mk precision (decodeBHist (encodeBHist radius))
            (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist hrow))
            (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
            (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius (decodeBHist (encodeBHist window))
              (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
              (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
              (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision row (decodeBHist (encodeBHist window))
              (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
              (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
              (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist radius)
      have hWindow :
          some (DyadicPrecisionUp.mk precision radius (decodeBHist (encodeBHist window))
            (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
            (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
            (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius window
              (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
              (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
              (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius row (decodeBHist (encodeBHist hrow))
              (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist window)
      have hHrow :
          some (DyadicPrecisionUp.mk precision radius window
            (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist contRow))
            (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
            (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius window hrow
              (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window row
              (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist hrow)
      have hContRow :
          some (DyadicPrecisionUp.mk precision radius window hrow
            (decodeBHist (encodeBHist contRow)) (decodeBHist (encodeBHist provenance))
            (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius window hrow contRow
              (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
              (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window hrow row
              (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
              (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist contRow)
      have hProvenance :
          some (DyadicPrecisionUp.mk precision radius window hrow contRow
            (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
            (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window hrow contRow row
              (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist provenance)
      have hCert :
          some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance
            (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance cert
              (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance row
              (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist cert)
      have hLedger :
          some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance cert
            (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance cert
              ledger) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window hrow contRow provenance cert row))
          (decode_encode_bhist ledger)
      exact Eq.trans hPrecision
        (Eq.trans hRadius
          (Eq.trans hWindow
            (Eq.trans hHrow
              (Eq.trans hContRow (Eq.trans hProvenance (Eq.trans hCert hLedger))))))

theorem DyadicPrecisionSchedule_namecert_obligations_toEventFlow_injective
    {x y : DyadicPrecisionUp} :
    DyadicPrecisionSchedule_namecert_obligations_toEventFlow x =
      DyadicPrecisionSchedule_namecert_obligations_toEventFlow y → x = y := by
  intro heq
  have hread :
      DyadicPrecisionSchedule_namecert_obligations_fromEventFlow
          (DyadicPrecisionSchedule_namecert_obligations_toEventFlow x) =
        DyadicPrecisionSchedule_namecert_obligations_fromEventFlow
          (DyadicPrecisionSchedule_namecert_obligations_toEventFlow y) :=
    congrArg DyadicPrecisionSchedule_namecert_obligations_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicPrecisionSchedule_namecert_obligations_round_trip x).symm
      (Eq.trans hread (DyadicPrecisionSchedule_namecert_obligations_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DyadicPrecisionSchedule_namecert_obligations_toEventFlow
  fromEventFlow := DyadicPrecisionSchedule_namecert_obligations_fromEventFlow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  round_trip := by
    intro x
    change DyadicPrecisionSchedule_namecert_obligations_fromEventFlow
      (DyadicPrecisionSchedule_namecert_obligations_toEventFlow x) = some x
    exact DyadicPrecisionSchedule_namecert_obligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicPrecisionSchedule_namecert_obligations_toEventFlow_injective heq)

theorem DyadicPrecisionSchedule_namecert_obligations [AskSetup] [PackageSetup]
    {n rho window hrow contRow provenance cert ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory n -> UnaryHistory rho -> UnaryHistory window -> UnaryHistory hrow ->
      UnaryHistory contRow -> UnaryHistory provenance -> Cont n rho window ->
        Cont window hrow contRow -> Cont contRow provenance cert ->
          Cont cert provenance ledger -> PkgSig bundle ledger pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row ledger ∧ UnaryHistory n ∧ UnaryHistory rho ∧
                  UnaryHistory window ∧ UnaryHistory hrow ∧ UnaryHistory contRow ∧
                    UnaryHistory provenance ∧ PkgSig bundle ledger pkg)
              (fun row : BHist =>
                hsame row ledger ∧ UnaryHistory n ∧ UnaryHistory rho ∧
                  UnaryHistory window ∧ UnaryHistory hrow ∧ UnaryHistory contRow ∧
                    UnaryHistory provenance ∧ PkgSig bundle ledger pkg)
              (fun row : BHist =>
                hsame row ledger ∧ UnaryHistory n ∧ UnaryHistory rho ∧
                  UnaryHistory window ∧ UnaryHistory hrow ∧ UnaryHistory contRow ∧
                    UnaryHistory provenance ∧ PkgSig bundle ledger pkg)
              hsame := by
  intro nUnary rhoUnary windowUnary hrowUnary contRowUnary provenanceUnary precisionRoute
    scheduleRoute certRoute ledgerRoute pkgSig
  have certUnary : UnaryHistory cert :=
    unary_cont_closed contRowUnary provenanceUnary certRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed certUnary provenanceUnary ledgerRoute
  exact {
    core := {
      carrier_inhabited := by
        exact Exists.intro ledger
          (And.intro (hsame_refl ledger)
            (And.intro nUnary
              (And.intro rhoUnary
                (And.intro windowUnary
                  (And.intro hrowUnary
                    (And.intro contRowUnary (And.intro provenanceUnary pkgSig)))))))
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (And.intro source.right.left
            (And.intro source.right.right.left
              (And.intro source.right.right.right.left
                (And.intro source.right.right.right.right.left
                  (And.intro source.right.right.right.right.right.left
                    (And.intro source.right.right.right.right.right.right.left
                      source.right.right.right.right.right.right.right))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def DyadicPrecisionSchedule_namecert_obligations_taste_gate :
    ChapterTasteGate DyadicPrecisionUp :=
  dyadicPrecisionChapterTasteGate

end BEDC.Derived.DyadicPrecisionUp
