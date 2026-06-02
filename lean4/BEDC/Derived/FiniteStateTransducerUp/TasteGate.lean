import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

def BEDC.Derived.FiniteStateTransducerUp [BEDC.FKernel.Ask.AskSetup]
    [BEDC.FKernel.Package.PackageSetup]
    (Q Sigma Gamma delta lambda q0 w rho o H C P N : BEDC.FKernel.Hist.BHist)
    (_bundle : BEDC.FKernel.Bundle.ProbeBundle BEDC.FKernel.Ask.ProbeName)
    (pkg : BEDC.FKernel.Package.Pkg) : Prop :=
  BEDC.FKernel.Unary.UnaryHistory Q ∧
    BEDC.FKernel.Unary.UnaryHistory Sigma ∧
      BEDC.FKernel.Unary.UnaryHistory Gamma ∧
        BEDC.FKernel.Unary.UnaryHistory delta ∧
          BEDC.FKernel.Unary.UnaryHistory lambda ∧
            BEDC.FKernel.Unary.UnaryHistory q0 ∧
              BEDC.FKernel.Unary.UnaryHistory w ∧
                BEDC.FKernel.Unary.UnaryHistory rho ∧
                  BEDC.FKernel.Unary.UnaryHistory o ∧
                    BEDC.FKernel.Unary.UnaryHistory H ∧
                      BEDC.FKernel.Cont.Cont w rho o ∧
                        BEDC.FKernel.Cont.Cont H C N ∧
                          BEDC.FKernel.Package.PkgSig
                            (BEDC.FKernel.Bundle.ProbeBundle.Bnil : BEDC.FKernel.Bundle.ProbeBundle BEDC.FKernel.Ask.ProbeName)
                            P pkg

namespace BEDC.Derived.FiniteStateTransducerUp

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

inductive FiniteStateTransducerUp : Type where
  | mk :
      (Q Sigma Gamma delta lambda q0 w rho o H C P N : BHist) →
        FiniteStateTransducerUp
  deriving DecidableEq

def finiteStateTransducerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteStateTransducerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteStateTransducerEncodeBHist h

def finiteStateTransducerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteStateTransducerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteStateTransducerDecodeBHist tail)

private theorem finiteStateTransducerDecode_encode_bhist :
    ∀ h : BHist,
      finiteStateTransducerDecodeBHist (finiteStateTransducerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem finiteStateTransducer_mk_congr
    {Q Q' Sigma Sigma' Gamma Gamma' delta delta' lambda lambda' q0 q0' w w'
      rho rho' o o' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q)
    (hSigma : Sigma' = Sigma)
    (hGamma : Gamma' = Gamma)
    (hdelta : delta' = delta)
    (hlambda : lambda' = lambda)
    (hq0 : q0' = q0)
    (hw : w' = w)
    (hrho : rho' = rho)
    (ho : o' = o)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    FiniteStateTransducerUp.mk Q' Sigma' Gamma' delta' lambda' q0' w' rho' o' H' C' P' N' =
      FiniteStateTransducerUp.mk Q Sigma Gamma delta lambda q0 w rho o H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hSigma
  cases hGamma
  cases hdelta
  cases hlambda
  cases hq0
  cases hw
  cases hrho
  cases ho
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def finiteStateTransducerToEventFlow : FiniteStateTransducerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteStateTransducerUp.mk Q Sigma Gamma delta lambda q0 w rho o H C P N =>
      [finiteStateTransducerEncodeBHist Q,
        finiteStateTransducerEncodeBHist Sigma,
        finiteStateTransducerEncodeBHist Gamma,
        finiteStateTransducerEncodeBHist delta,
        finiteStateTransducerEncodeBHist lambda,
        finiteStateTransducerEncodeBHist q0,
        finiteStateTransducerEncodeBHist w,
        finiteStateTransducerEncodeBHist rho,
        finiteStateTransducerEncodeBHist o,
        finiteStateTransducerEncodeBHist H,
        finiteStateTransducerEncodeBHist C,
        finiteStateTransducerEncodeBHist P,
        finiteStateTransducerEncodeBHist N]

def finiteStateTransducerFromEventFlow : EventFlow → Option FiniteStateTransducerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest =>
      match rest with
      | [] => none
      | Sigma :: rest =>
          match rest with
          | [] => none
          | Gamma :: rest =>
              match rest with
              | [] => none
              | delta :: rest =>
                  match rest with
                  | [] => none
                  | lambda :: rest =>
                      match rest with
                      | [] => none
                      | q0 :: rest =>
                          match rest with
                          | [] => none
                          | w :: rest =>
                              match rest with
                              | [] => none
                              | rho :: rest =>
                                  match rest with
                                  | [] => none
                                  | o :: rest =>
                                      match rest with
                                      | [] => none
                                      | H :: rest =>
                                          match rest with
                                          | [] => none
                                          | C :: rest =>
                                              match rest with
                                              | [] => none
                                              | P :: rest =>
                                                  match rest with
                                                  | [] => none
                                                  | N :: rest =>
                                                      match rest with
                                                      | [] =>
                                                          some
                                                            (FiniteStateTransducerUp.mk
                                                              (finiteStateTransducerDecodeBHist Q)
                                                              (finiteStateTransducerDecodeBHist Sigma)
                                                              (finiteStateTransducerDecodeBHist Gamma)
                                                              (finiteStateTransducerDecodeBHist delta)
                                                              (finiteStateTransducerDecodeBHist lambda)
                                                              (finiteStateTransducerDecodeBHist q0)
                                                              (finiteStateTransducerDecodeBHist w)
                                                              (finiteStateTransducerDecodeBHist rho)
                                                              (finiteStateTransducerDecodeBHist o)
                                                              (finiteStateTransducerDecodeBHist H)
                                                              (finiteStateTransducerDecodeBHist C)
                                                              (finiteStateTransducerDecodeBHist P)
                                                              (finiteStateTransducerDecodeBHist N))
                                                      | _ :: _ => none

def finiteStateTransducerFields : FiniteStateTransducerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteStateTransducerUp.mk Q Sigma Gamma delta lambda q0 w rho o H C P N =>
      [Q, Sigma, Gamma, delta, lambda, q0, w, rho, o, H, C, P, N]

private theorem finiteStateTransducer_round_trip :
    ∀ x : FiniteStateTransducerUp,
      finiteStateTransducerFromEventFlow (finiteStateTransducerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q Sigma Gamma delta lambda q0 w rho o H C P N =>
      exact
        congrArg some
          (finiteStateTransducer_mk_congr
            (finiteStateTransducerDecode_encode_bhist Q)
            (finiteStateTransducerDecode_encode_bhist Sigma)
            (finiteStateTransducerDecode_encode_bhist Gamma)
            (finiteStateTransducerDecode_encode_bhist delta)
            (finiteStateTransducerDecode_encode_bhist lambda)
            (finiteStateTransducerDecode_encode_bhist q0)
            (finiteStateTransducerDecode_encode_bhist w)
            (finiteStateTransducerDecode_encode_bhist rho)
            (finiteStateTransducerDecode_encode_bhist o)
            (finiteStateTransducerDecode_encode_bhist H)
            (finiteStateTransducerDecode_encode_bhist C)
            (finiteStateTransducerDecode_encode_bhist P)
            (finiteStateTransducerDecode_encode_bhist N))

private theorem finiteStateTransducerToEventFlow_injective
    {x y : FiniteStateTransducerUp} :
    finiteStateTransducerToEventFlow x = finiteStateTransducerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteStateTransducerFromEventFlow (finiteStateTransducerToEventFlow x) =
        finiteStateTransducerFromEventFlow (finiteStateTransducerToEventFlow y) :=
    congrArg finiteStateTransducerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteStateTransducer_round_trip x).symm
      (Eq.trans hread (finiteStateTransducer_round_trip y)))

private theorem finiteStateTransducerFields_faithful :
    ∀ x y : FiniteStateTransducerUp,
      finiteStateTransducerFields x = finiteStateTransducerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Q1 Sigma1 Gamma1 delta1 lambda1 q01 w1 rho1 o1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 Sigma2 Gamma2 delta2 lambda2 q02 w2 rho2 o2 H2 C2 P2 N2 =>
          cases h
          rfl

instance finiteStateTransducerBHistCarrier :
    BHistCarrier FiniteStateTransducerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteStateTransducerToEventFlow
  fromEventFlow := finiteStateTransducerFromEventFlow

instance finiteStateTransducerChapterTasteGate :
    ChapterTasteGate FiniteStateTransducerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteStateTransducerFromEventFlow (finiteStateTransducerToEventFlow x) = some x
    exact finiteStateTransducer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteStateTransducerToEventFlow_injective heq)

instance finiteStateTransducerFieldFaithful :
    FieldFaithful FiniteStateTransducerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteStateTransducerFields
  field_faithful := finiteStateTransducerFields_faithful

instance finiteStateTransducerNontrivial :
    Nontrivial FiniteStateTransducerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteStateTransducerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FiniteStateTransducerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteStateTransducerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem FiniteStateTransducerTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteStateTransducerDecodeBHist (finiteStateTransducerEncodeBHist h) = h) ∧
      (∀ x : FiniteStateTransducerUp,
        finiteStateTransducerFromEventFlow (finiteStateTransducerToEventFlow x) = some x) ∧
        (∀ x y : FiniteStateTransducerUp,
          finiteStateTransducerToEventFlow x = finiteStateTransducerToEventFlow y →
            x = y) ∧
          finiteStateTransducerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact finiteStateTransducerDecode_encode_bhist h
  · constructor
    · intro x
      exact finiteStateTransducer_round_trip x
    · constructor
      · intro x y heq
        exact finiteStateTransducerToEventFlow_injective heq
      · rfl

theorem FiniteStateTransducerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q Sigma Gamma delta lambda q0 w rho o H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.FiniteStateTransducerUp Q Sigma Gamma delta lambda q0 w rho o H C P N
        bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            BEDC.Derived.FiniteStateTransducerUp Q Sigma Gamma delta lambda q0 w rho o H C
                P N bundle pkg ∧ hsame row N)
          (fun row : BHist =>
            BEDC.Derived.FiniteStateTransducerUp Q Sigma Gamma delta lambda q0 w rho o H C
                P N bundle pkg ∧ hsame row N)
          (fun row : BHist =>
            BEDC.Derived.FiniteStateTransducerUp Q Sigma Gamma delta lambda q0 w rho o H C
                P N bundle pkg ∧ hsame row N)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro accepted
  let SourceSpec : BHist → Prop := fun row =>
    BEDC.Derived.FiniteStateTransducerUp Q Sigma Gamma delta lambda q0 w rho o H C P N
      bundle pkg ∧ hsame row N
  have sourceN : SourceSpec N := ⟨accepted, hsame_refl N⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.FiniteStateTransducerUp
