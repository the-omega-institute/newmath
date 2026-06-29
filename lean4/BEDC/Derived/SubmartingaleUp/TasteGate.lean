import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
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
