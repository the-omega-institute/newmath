import BEDC.Derived.RHRoute.WeilFixed2x2PacketPSD
import BEDC.Derived.RHRoute.WeilPrimeSensitivePacket

namespace BEDC.Derived.RHRoute.WeilResidualFarkasCut

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.WeilFixed2x2PacketPSD
open BEDC.Derived.RHRoute.WeilPrimeSensitivePacket

abbrev Rat : Type :=
  RatNum

structure Vec2 where
  c1 : Rat
  c2 : Rat

structure Sym2 where
  m11 : Rat
  m12 : Rat
  m22 : Rat

def q2 (M : Sym2) (x : Vec2) : Rat :=
  quad2 M.m11 M.m12 M.m22 x.c1 x.c2

structure Packet2 where
  M1 : Sym2
  psd : Fixed2x2Cert
  psd_link :
    (M1.m11 = psd.b11) ∧
      (M1.m12 = psd.b12) ∧
        (M1.m22 = psd.b22)

theorem packet_psd (P : Packet2) (x : Vec2) :
    ratLe ratZero (q2 P.M1 x) := by
  rcases P.psd_link with ⟨h11, h12, h22⟩
  unfold q2
  rw [h11, h12, h22]
  exact fixed2x2_cert_psd P.psd x.c1 x.c2

def sumList : List Rat -> Rat :=
  List.foldr ratAdd ratZero

def zipWithRat (f : Rat -> Rat -> Rat) : List Rat -> List Rat -> List Rat
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => f a b :: zipWithRat f as bs

def zipWithAtom (f : Rat -> Sym2 -> Rat) : List Rat -> List Sym2 -> List Rat
  | [], _ => []
  | _, [] => []
  | l :: ls, a :: atoms => f l a :: zipWithAtom f ls atoms

structure ResidualClass where
  atoms : List Sym2
  offMass : List Rat
  admissible : List Rat -> Prop

def residualQ (C : ResidualClass) (lam : List Rat) (x : Vec2) : Rat :=
  sumList (zipWithAtom (fun l a => ratMul l (q2 a x)) lam C.atoms)

def Skeleton (C : ResidualClass) (lam : List Rat) : Prop :=
  (∀ l, l ∈ lam -> ratLe ratZero l) ∧
    ratLt ratZero (sumList (zipWithRat ratMul lam C.offMass)) ∧
      C.admissible lam

structure NonVacuousSkeleton (C : ResidualClass) where
  lam : List Rat
  witness : Skeleton C lam

def VisibleAt
    (P : Packet2) (C : ResidualClass) (x : Vec2)
    (kappa : Rat) (lam : List Rat) : Prop :=
  ratLe (ratAbs (ratSub (q2 P.M1 x) (residualQ C lam x))) kappa

structure ProjectionSepCert (C : ResidualClass) (x : Vec2) where
  eta : Rat
  kappa : Rat
  y : List Rat
  dualValue : Rat
  eta_pos : ratLt ratZero eta
  kappa_nonneg : ratLe ratZero kappa
  coeff_le :
    ∀ lam, Skeleton C lam -> ratLe (residualQ C lam x) dualValue
  rhs_le :
    ratLe dualValue (ratNeg (ratAdd eta kappa))
  rhs_le_neg_eta :
    ratLe
      (ratAdd (ratNeg (ratAdd eta kappa)) kappa)
      (ratNeg eta)

theorem residualQ_neg_of_sep
    {C : ResidualClass} {x : Vec2}
    (sep : ProjectionSepCert C x) (lam : List Rat)
    (adm : Skeleton C lam) :
    ratLe (residualQ C lam x) (ratNeg (ratAdd sep.eta sep.kappa)) :=
  ratLe_trans (sep.coeff_le lam adm) sep.rhs_le

private theorem ratSub_add_cancel_right_local (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratLe_of_neg_nonneg_local {x : Rat} :
    ratLe ratZero (ratNeg x) -> ratLe x ratZero := by
  intro h
  have subLe : ratLe (ratSub ratZero (ratNeg x)) ratZero :=
    ratSub_le_left_of_nonneg h
  have subEq :
      RatEq (ratSub ratZero (ratNeg x)) x := by
    unfold ratSub
    exact RatEq_trans _ _ _
      (ratZero_add_left (ratNeg (ratNeg x)))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local x)
  exact ratLe_respects subEq (RatEq_refl ratZero) subLe

theorem visible_upper_bound
    {P : Packet2} {C : ResidualClass} {x : Vec2}
    {kappa : Rat} {lam : List Rat}
    (vis : VisibleAt P C x kappa lam) :
    ratLe (q2 P.M1 x) (ratAdd (residualQ C lam x) kappa) := by
  unfold VisibleAt at vis
  have diffLeAbs :
      ratLe (ratSub (q2 P.M1 x) (residualQ C lam x))
        (ratAbs (ratSub (q2 P.M1 x) (residualQ C lam x))) :=
    BEDC.Derived.LocatedReal.ratLe_self_abs
      (ratSub (q2 P.M1 x) (residualQ C lam x))
  have diffLeKappa :
      ratLe (ratSub (q2 P.M1 x) (residualQ C lam x)) kappa :=
    ratLe_trans diffLeAbs vis
  have shifted :
      ratLe
        (ratAdd (ratSub (q2 P.M1 x) (residualQ C lam x))
          (residualQ C lam x))
        (ratAdd kappa (residualQ C lam x)) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := ratSub (q2 P.M1 x) (residualQ C lam x))
      (x' := kappa)
      (y := residualQ C lam x)
      diffLeKappa
  exact ratLe_respects
    (ratSub_add_cancel_right_local
      (q2 P.M1 x) (residualQ C lam x))
    (ratAdd_comm kappa (residualQ C lam x))
    shifted

theorem no_packet_visible_residual_closure
    (P : Packet2) (C : ResidualClass) (x : Vec2)
    (sep : ProjectionSepCert C x) :
    ¬ ∃ lam, Skeleton C lam ∧ VisibleAt P C x sep.kappa lam := by
  intro h
  rcases h with ⟨lam, adm, vis⟩
  have residualNeg :
      ratLe (residualQ C lam x) (ratNeg (ratAdd sep.eta sep.kappa)) :=
    residualQ_neg_of_sep sep lam adm
  have upperVisible :
      ratLe (q2 P.M1 x) (ratAdd (residualQ C lam x) sep.kappa) :=
    visible_upper_bound vis
  have addKappa :
      ratLe
        (ratAdd (residualQ C lam x) sep.kappa)
        (ratAdd (ratNeg (ratAdd sep.eta sep.kappa)) sep.kappa) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := residualQ C lam x)
      (x' := ratNeg (ratAdd sep.eta sep.kappa))
      (y := sep.kappa)
      residualNeg
  have packetLeNegEta :
      ratLe (q2 P.M1 x) (ratNeg sep.eta) :=
    ratLe_trans upperVisible (ratLe_trans addKappa sep.rhs_le_neg_eta)
  have packetNonneg : ratLe ratZero (q2 P.M1 x) :=
    packet_psd P x
  have negEtaNonneg : ratLe ratZero (ratNeg sep.eta) :=
    ratLe_trans packetNonneg packetLeNegEta
  have etaLeZero : ratLe sep.eta ratZero :=
    ratLe_of_neg_nonneg_local negEtaNonneg
  exact ratLt_not_ratLe_reverse sep.eta_pos etaLeZero

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          cases h
      | succ b =>
          intro h
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem zero_le_zero : ratLe ratZero ratZero :=
  ratLe_refl ratZero

private theorem zero_lt_one : ratLt ratZero ratOne :=
  ratLtBool_true_to_ratLt (by rfl)

private theorem neg_one_le_neg_one :
    ratLe (ratNeg ratOne) (ratNeg ratOne) :=
  ratLe_refl (ratNeg ratOne)

private theorem neg_two_le_neg_one :
    ratLe (ratAdd (ratNeg (ratAdd ratOne ratZero)) ratZero)
      (ratNeg ratOne) :=
  ratLeBool_true_to_ratLe (by rfl)

def canonicalCutPoint : Vec2 where
  c1 := ratOne
  c2 := ratZero

def canonicalPacketCert : Fixed2x2Cert where
  lo11 := ratOne
  hi11 := ratOne
  lo12 := ratZero
  hi12 := ratZero
  lo22 := ratOne
  hi22 := ratOne
  b11 := ratOne
  b12 := ratZero
  b22 := ratOne
  hord11 := ratLe_refl ratOne
  hord12 := zero_le_zero
  hord22 := ratLe_refl ratOne
  hlo11Nonneg := ratLt_to_ratLe zero_lt_one
  hlo22Nonneg := ratLt_to_ratLe zero_lt_one
  hdetCert := ratLeBool_true_to_ratLe (by rfl)
  hb11lo := ratLe_refl ratOne
  hb11hi := ratLe_refl ratOne
  hb12lo := zero_le_zero
  hb12hi := zero_le_zero
  hb22lo := ratLe_refl ratOne
  hb22hi := ratLe_refl ratOne

def canonicalPacket : Packet2 where
  M1 := { m11 := ratOne, m12 := ratZero, m22 := ratOne }
  psd := canonicalPacketCert
  psd_link := ⟨rfl, rfl, rfl⟩

def canonicalResidualAtom : Sym2 where
  m11 := ratNeg ratOne
  m12 := ratZero
  m22 := ratZero

def canonicalResidualClass : ResidualClass where
  atoms := [canonicalResidualAtom]
  offMass := [ratOne]
  admissible := fun lam => lam = [ratOne]

theorem canonical_skeleton :
    Skeleton canonicalResidualClass [ratOne] := by
  constructor
  · intro l h
    cases h with
    | head =>
        exact ratLt_to_ratLe zero_lt_one
    | tail _ htail =>
        cases htail
  · constructor
    · exact zero_lt_one
    · rfl

def canonicalNonVacuousSkeleton :
    NonVacuousSkeleton canonicalResidualClass where
  lam := [ratOne]
  witness := canonical_skeleton

theorem canonical_residual_cut
    (lam : List Rat) (adm : Skeleton canonicalResidualClass lam) :
    ratLe
      (residualQ canonicalResidualClass lam canonicalCutPoint)
      (ratNeg (ratAdd ratOne ratZero)) := by
  have hLam : lam = [ratOne] := adm.right.right
  cases hLam
  exact neg_one_le_neg_one

def canonicalProjectionSepCert :
    ProjectionSepCert canonicalResidualClass canonicalCutPoint where
  eta := ratOne
  kappa := ratZero
  y := [ratOne]
  dualValue := ratNeg (ratAdd ratOne ratZero)
  eta_pos := zero_lt_one
  kappa_nonneg := zero_le_zero
  coeff_le := canonical_residual_cut
  rhs_le := ratLe_refl (ratNeg (ratAdd ratOne ratZero))
  rhs_le_neg_eta := neg_two_le_neg_one

theorem canonical_no_packet_visible_residual_closure :
    ¬ ∃ lam,
      Skeleton canonicalResidualClass lam ∧
        VisibleAt canonicalPacket canonicalResidualClass canonicalCutPoint
          canonicalProjectionSepCert.kappa lam :=
  no_packet_visible_residual_closure
    canonicalPacket canonicalResidualClass canonicalCutPoint
    canonicalProjectionSepCert

end BEDC.Derived.RHRoute.WeilResidualFarkasCut
