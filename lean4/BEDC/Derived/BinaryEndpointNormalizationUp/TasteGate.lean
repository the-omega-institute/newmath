import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinaryEndpointNormalizationUp

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

inductive BinaryEndpointNormalizationUp : Type where
  | mk (L R K D A W Q S H C P N : BHist) : BinaryEndpointNormalizationUp
  deriving DecidableEq

def binaryEndpointNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: binaryEndpointNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: binaryEndpointNormalizationEncodeBHist h

def binaryEndpointNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (binaryEndpointNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (binaryEndpointNormalizationDecodeBHist tail)

private theorem BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      binaryEndpointNormalizationDecodeBHist
        (binaryEndpointNormalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem BinaryEndpointNormalizationTasteGate_single_carrier_alignment_mk_congr
    {L1 R1 K1 D1 A1 W1 Q1 S1 H1 C1 P1 N1 L2 R2 K2 D2 A2 W2 Q2 S2 H2 C2 P2 N2 :
      BHist}
    (hL : L1 = L2)
    (hR : R1 = R2)
    (hK : K1 = K2)
    (hD : D1 = D2)
    (hA : A1 = A2)
    (hW : W1 = W2)
    (hQ : Q1 = Q2)
    (hS : S1 = S2)
    (hH : H1 = H2)
    (hC : C1 = C2)
    (hP : P1 = P2)
    (hN : N1 = N2) :
    BinaryEndpointNormalizationUp.mk L1 R1 K1 D1 A1 W1 Q1 S1 H1 C1 P1 N1 =
      BinaryEndpointNormalizationUp.mk L2 R2 K2 D2 A2 W2 Q2 S2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hR
  cases hK
  cases hD
  cases hA
  cases hW
  cases hQ
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def binaryEndpointNormalizationToEventFlow : BinaryEndpointNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N =>
      [[BMark.b0],
        binaryEndpointNormalizationEncodeBHist L,
        [BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        binaryEndpointNormalizationEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        binaryEndpointNormalizationEncodeBHist N]

def binaryEndpointNormalizationPayloads : EventFlow → Option EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _ :: rest =>
      match rest with
      | [] => none
      | row :: tail =>
          match binaryEndpointNormalizationPayloads tail with
          | some rows => some (row :: rows)
          | none => none

def binaryEndpointNormalizationFromPayloads :
    EventFlow → Option BinaryEndpointNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restR =>
      match restR with
      | [] => none
      | R :: restK =>
          match restK with
          | [] => none
          | K :: restD =>
              match restD with
              | [] => none
              | D :: restA =>
                  match restA with
                  | [] => none
                  | A :: restW =>
                      match restW with
                      | [] => none
                      | W :: restQ =>
                          match restQ with
                          | [] => none
                          | Q :: restS =>
                              match restS with
                              | [] => none
                              | S :: restH =>
                                  match restH with
                                  | [] => none
                                  | H :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restP =>
                                          match restP with
                                          | [] => none
                                          | P :: restN =>
                                              match restN with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some (BinaryEndpointNormalizationUp.mk
                                                        (binaryEndpointNormalizationDecodeBHist L)
                                                        (binaryEndpointNormalizationDecodeBHist R)
                                                        (binaryEndpointNormalizationDecodeBHist K)
                                                        (binaryEndpointNormalizationDecodeBHist D)
                                                        (binaryEndpointNormalizationDecodeBHist A)
                                                        (binaryEndpointNormalizationDecodeBHist W)
                                                        (binaryEndpointNormalizationDecodeBHist Q)
                                                        (binaryEndpointNormalizationDecodeBHist S)
                                                        (binaryEndpointNormalizationDecodeBHist H)
                                                        (binaryEndpointNormalizationDecodeBHist C)
                                                        (binaryEndpointNormalizationDecodeBHist P)
                                                        (binaryEndpointNormalizationDecodeBHist N))
                                                  | _ :: _ => none

def binaryEndpointNormalizationFromEventFlow
    (flow : EventFlow) : Option BinaryEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match binaryEndpointNormalizationPayloads flow with
  | some rows => binaryEndpointNormalizationFromPayloads rows
  | none => none

private theorem BinaryEndpointNormalizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BinaryEndpointNormalizationUp,
      binaryEndpointNormalizationFromEventFlow
        (binaryEndpointNormalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R K D A W Q S H C P N =>
      change
        some
          (BinaryEndpointNormalizationUp.mk
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist L))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist R))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist K))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist D))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist A))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist W))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist Q))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist S))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist H))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist C))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist P))
            (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationEncodeBHist N))) =
          some (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N)
      exact congrArg some
        (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_mk_congr
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode L)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode R)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode K)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode D)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode A)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode W)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode Q)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode S)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode H)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode C)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode P)
          (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode N))

private theorem BinaryEndpointNormalizationTasteGate_single_carrier_alignment_injective
    {x y : BinaryEndpointNormalizationUp} :
    binaryEndpointNormalizationToEventFlow x =
      binaryEndpointNormalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      binaryEndpointNormalizationFromEventFlow (binaryEndpointNormalizationToEventFlow x) =
        binaryEndpointNormalizationFromEventFlow (binaryEndpointNormalizationToEventFlow y) :=
    congrArg binaryEndpointNormalizationFromEventFlow heq
  exact Option.some.inj
      (Eq.trans
        (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_round_trip y)))

instance binaryEndpointNormalizationBHistCarrier :
    BHistCarrier BinaryEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := binaryEndpointNormalizationToEventFlow
  fromEventFlow := binaryEndpointNormalizationFromEventFlow

instance binaryEndpointNormalizationChapterTasteGate :
    ChapterTasteGate BinaryEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      binaryEndpointNormalizationFromEventFlow
        (binaryEndpointNormalizationToEventFlow x) = some x
    exact BinaryEndpointNormalizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BinaryEndpointNormalizationTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BinaryEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  binaryEndpointNormalizationChapterTasteGate

theorem BinaryEndpointNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      binaryEndpointNormalizationDecodeBHist
        (binaryEndpointNormalizationEncodeBHist h) = h) ∧
      (∀ x : BinaryEndpointNormalizationUp,
        binaryEndpointNormalizationFromEventFlow
          (binaryEndpointNormalizationToEventFlow x) = some x) ∧
      (∀ x y : BinaryEndpointNormalizationUp,
        binaryEndpointNormalizationToEventFlow x =
          binaryEndpointNormalizationToEventFlow y → x = y) ∧
      binaryEndpointNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro BinaryEndpointNormalizationTasteGate_single_carrier_alignment_decode
      (And.intro BinaryEndpointNormalizationTasteGate_single_carrier_alignment_round_trip
        (And.intro
          (fun x y heq =>
            BinaryEndpointNormalizationTasteGate_single_carrier_alignment_injective heq)
          rfl))

theorem BinaryEndpointNormalizationNameCertObligations [AskSetup] [PackageSetup]
    {L R K D A W Q S H C P N carryRead approxRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory K ->
          UnaryHistory D ->
            UnaryHistory A ->
              UnaryHistory W ->
                UnaryHistory Q ->
                  UnaryHistory S ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory P ->
                          UnaryHistory N ->
                            Cont W D carryRead ->
                              Cont carryRead A approxRead ->
                                Cont approxRead Q sealRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle sealRead pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row sealRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row L ∨ hsame row R ∨ hsame row K ∨
                                              hsame row D ∨ hsame row A ∨ hsame row W ∨
                                                hsame row Q ∨ hsame row S ∨
                                                  hsame row H ∨ hsame row C ∨
                                                    hsame row P ∨ hsame row N ∨
                                                      hsame row carryRead ∨
                                                        hsame row approxRead ∨
                                                          hsame row sealRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont W D carryRead ∧
                                              Cont carryRead A approxRead ∧
                                                Cont approxRead Q sealRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle sealRead pkg)
                                          hsame ∧
                                        UnaryHistory carryRead ∧
                                          UnaryHistory approxRead ∧
                                            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _lUnary _rUnary _kUnary dUnary aUnary wUnary qUnary _sUnary _hUnary _cUnary
    _pUnary _nUnary carryRoute approxRoute sealRoute provenancePkg sealPkg
  have carryUnary : UnaryHistory carryRead :=
    unary_cont_closed wUnary dUnary carryRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed carryUnary aUnary approxRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approxUnary qUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row K ∨ hsame row D ∨
              hsame row A ∨ hsame row W ∨ hsame row Q ∨ hsame row S ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row carryRead ∨ hsame row approxRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D carryRead ∧ Cont carryRead A approxRead ∧
              Cont approxRead Q sealRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carryRoute, approxRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, carryUnary, approxUnary, sealUnary⟩

end BEDC.Derived.BinaryEndpointNormalizationUp
