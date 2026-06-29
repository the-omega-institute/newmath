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

namespace BEDC.Derived.SubmartingaleUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubmartingaleUp : Type where
  | mk (Omega R C F X E I T H K P N : BHist) : SubmartingaleUp
  deriving DecidableEq

def submartingaleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: submartingaleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: submartingaleEncodeBHist h

def submartingaleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (submartingaleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (submartingaleDecodeBHist tail)

private theorem submartingaleDecode_encode :
    ∀ h : BHist, submartingaleDecodeBHist (submartingaleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def submartingaleFields : SubmartingaleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubmartingaleUp.mk Omega R C F X E I T H K P N =>
      [Omega, R, C, F, X, E, I, T, H, K, P, N]

def submartingaleToEventFlow : SubmartingaleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (submartingaleFields x).map submartingaleEncodeBHist

def submartingaleFromEventFlow : EventFlow → Option SubmartingaleUp
  -- BEDC touchpoint anchor: BHist BMark
  | Omega :: restOmega =>
      match restOmega with
      | R :: restR =>
          match restR with
          | C :: restC =>
              match restC with
              | F :: restF =>
                  match restF with
                  | X :: restX =>
                      match restX with
                      | E :: restE =>
                          match restE with
                          | I :: restI =>
                              match restI with
                              | T :: restT =>
                                  match restT with
                                  | H :: restH =>
                                      match restH with
                                      | K :: restK =>
                                          match restK with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (SubmartingaleUp.mk
                                                          (submartingaleDecodeBHist Omega)
                                                          (submartingaleDecodeBHist R)
                                                          (submartingaleDecodeBHist C)
                                                          (submartingaleDecodeBHist F)
                                                          (submartingaleDecodeBHist X)
                                                          (submartingaleDecodeBHist E)
                                                          (submartingaleDecodeBHist I)
                                                          (submartingaleDecodeBHist T)
                                                          (submartingaleDecodeBHist H)
                                                          (submartingaleDecodeBHist K)
                                                          (submartingaleDecodeBHist P)
                                                          (submartingaleDecodeBHist N))
                                                  | _ :: _ => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem submartingale_mk_congr
    {Omega Omega' R R' C C' F F' X X' E E' I I' T T' H H' K K' P P' N N' :
      BHist}
    (hOmega : Omega' = Omega) (hR : R' = R) (hC : C' = C) (hF : F' = F)
    (hX : X' = X) (hE : E' = E) (hI : I' = I) (hT : T' = T)
    (hH : H' = H) (hK : K' = K) (hP : P' = P) (hN : N' = N) :
    SubmartingaleUp.mk Omega' R' C' F' X' E' I' T' H' K' P' N' =
      SubmartingaleUp.mk Omega R C F X E I T H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hOmega
  cases hR
  cases hC
  cases hF
  cases hX
  cases hE
  cases hI
  cases hT
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

private theorem submartingale_round_trip :
    ∀ x : SubmartingaleUp,
      submartingaleFromEventFlow (submartingaleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Omega R C F X E I T H K P N =>
      exact
        congrArg some
          (submartingale_mk_congr
            (submartingaleDecode_encode Omega)
            (submartingaleDecode_encode R)
            (submartingaleDecode_encode C)
            (submartingaleDecode_encode F)
            (submartingaleDecode_encode X)
            (submartingaleDecode_encode E)
            (submartingaleDecode_encode I)
            (submartingaleDecode_encode T)
            (submartingaleDecode_encode H)
            (submartingaleDecode_encode K)
            (submartingaleDecode_encode P)
            (submartingaleDecode_encode N))

private theorem submartingaleToEventFlow_injective {x y : SubmartingaleUp} :
    submartingaleToEventFlow x = submartingaleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      submartingaleFromEventFlow (submartingaleToEventFlow x) =
        submartingaleFromEventFlow (submartingaleToEventFlow y) :=
    congrArg submartingaleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (submartingale_round_trip x).symm
      (Eq.trans hread (submartingale_round_trip y)))

instance submartingaleBHistCarrier : BHistCarrier SubmartingaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := submartingaleToEventFlow
  fromEventFlow := submartingaleFromEventFlow

instance submartingaleChapterTasteGate : ChapterTasteGate SubmartingaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change submartingaleFromEventFlow (submartingaleToEventFlow x) = some x
    exact submartingale_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (submartingaleToEventFlow_injective heq)

theorem SubmartingaleTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SubmartingaleUp) ∧
      Nonempty (ChapterTasteGate SubmartingaleUp) ∧
      (∀ h : BHist, submartingaleDecodeBHist (submartingaleEncodeBHist h) = h) ∧
      (∀ x : SubmartingaleUp,
        submartingaleFromEventFlow (submartingaleToEventFlow x) = some x) ∧
      submartingaleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨submartingaleBHistCarrier⟩,
      ⟨submartingaleChapterTasteGate⟩,
      submartingaleDecode_encode,
      submartingale_round_trip,
      rfl⟩

end BEDC.Derived.SubmartingaleUp.TasteGate

namespace BEDC.Derived.SubmartingaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubmartingaleCarrier [AskSetup] [PackageSetup]
    (omega randomVar condExp filtration endpoint expectation comparison time transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory omega ∧ UnaryHistory randomVar ∧ UnaryHistory condExp ∧
    UnaryHistory filtration ∧ UnaryHistory endpoint ∧ UnaryHistory expectation ∧
      UnaryHistory comparison ∧ UnaryHistory time ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle localName pkg

theorem SubmartingaleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {omega randomVar condExp filtration endpoint expectation comparison time transport replay
      provenance localName comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubmartingaleCarrier omega randomVar condExp filtration endpoint expectation comparison time
        transport replay provenance localName bundle pkg →
      Cont endpoint expectation comparisonRead →
        PkgSig bundle comparisonRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row omega ∨ hsame row randomVar ∨ hsame row condExp ∨
                  hsame row filtration ∨ hsame row endpoint ∨ hsame row expectation ∨
                    hsame row comparison ∨ hsame row time ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                        hsame row comparisonRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont endpoint expectation comparisonRead ∧
                  PkgSig bundle comparisonRead pkg)
              hsame ∧
            UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier comparisonRoute comparisonPkg
  obtain ⟨_omegaUnary, _randomVarUnary, _condExpUnary, _filtrationUnary, endpointUnary,
    expectationUnary, _comparisonUnary, _timeUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _localNamePkg⟩ := carrier
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed endpointUnary expectationUnary comparisonRoute
  have sourceComparisonRead :
      (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row) comparisonRead := by
    exact ⟨hsame_refl comparisonRead, comparisonReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row omega ∨ hsame row randomVar ∨ hsame row condExp ∨
              hsame row filtration ∨ hsame row endpoint ∨ hsame row expectation ∨
                hsame row comparison ∨ hsame row time ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                    hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint expectation comparisonRead ∧
              PkgSig bundle comparisonRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead sourceComparisonRead
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
      exact ⟨source.right, comparisonRoute, comparisonPkg⟩
  }
  exact ⟨cert, comparisonReadUnary⟩

end BEDC.Derived.SubmartingaleUp
