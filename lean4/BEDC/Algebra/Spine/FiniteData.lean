import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Algebra.Rel.Basic
import BEDC.Algebra.FiniteFold

namespace BEDC.Algebra.Spine.FiniteData

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Algebra.Rel

abbrev Hist := BHist

def emp : Hist := BHist.Empty
def Ezero (h : Hist) : Hist := BHist.e0 h
def Eone (h : Hist) : Hist := BHist.e1 h
abbrev ContR := Cont

structure CarrierUp where
  carrier : Hist -> Prop
  same : Hist -> Hist -> Prop
  same_equiv : RelEquiv { h : Hist // carrier h }
  same_left_carrier : forall {h k : Hist}, same h k -> carrier h
  same_right_carrier : forall {h k : Hist}, same h k -> carrier k
  same_equiv_sound :
    forall {h k : Hist} (hh : carrier h) (hk : carrier k),
      same_equiv.rel ⟨h, hh⟩ ⟨k, hk⟩ -> same h k
  same_equiv_complete :
    forall {h k : Hist} (hh : carrier h) (hk : carrier k),
      same h k -> same_equiv.rel ⟨h, hh⟩ ⟨k, hk⟩

namespace CarrierUp

theorem same_refl (A : CarrierUp) {h : Hist} (hh : A.carrier h) :
    A.same h h :=
  A.same_equiv_sound hh hh (A.same_equiv.refl ⟨h, hh⟩)

theorem same_symm (A : CarrierUp) {h k : Hist}
    (hh : A.carrier h) (hk : A.carrier k) :
    A.same h k -> A.same k h := by
  intro sameHK
  exact A.same_equiv_sound hk hh
    (A.same_equiv.symm (A.same_equiv_complete hh hk sameHK))

theorem same_trans (A : CarrierUp) {h k r : Hist}
    (hh : A.carrier h) (hk : A.carrier k) (hr : A.carrier r) :
    A.same h k -> A.same k r -> A.same h r := by
  intro sameHK sameKR
  exact A.same_equiv_sound hh hr
    (A.same_equiv.trans
      (A.same_equiv_complete hh hk sameHK)
      (A.same_equiv_complete hk hr sameKR))

theorem carrier_hsame_transport (A : CarrierUp) {h k : Hist} :
    hsame h k -> A.carrier h -> A.carrier k := by
  intro sameHK hh
  cases sameHK
  exact hh

theorem same_of_hsame (A : CarrierUp) {h k : Hist}
    (hh : A.carrier h) (hk : A.carrier k) :
    hsame h k -> A.same h k := by
  intro sameHK
  cases sameHK
  exact A.same_refl hh

end CarrierUp

structure FinDataConstr (A : CarrierUp) where
  witness : Hist
  witness_carrier : A.carrier witness

structure FinDataElim (A : CarrierUp) where
  expose : forall {h : Hist}, A.carrier h -> A.carrier h

structure FinDataStability (A : CarrierUp) where
  hsame_transport : forall {h k : Hist}, hsame h k -> A.carrier h -> A.carrier k
  same_refl_row : forall {h : Hist}, A.carrier h -> A.same h h

structure FinDataLedger (A : CarrierUp) where
  carrier_witness : exists h : Hist, A.carrier h
  classifier_reflexive : forall {h : Hist}, A.carrier h -> A.same h h

structure FinDataIface (A : CarrierUp) where
  constr : FinDataConstr A
  elim : FinDataElim A
  stab : FinDataStability A
  ledger : FinDataLedger A
  cert : NameCert A.carrier A.same

def carrier_name_cert (A : CarrierUp) (w : Hist) (hw : A.carrier w) :
    NameCert A.carrier A.same where
  carrier_inhabited := ⟨w, hw⟩
  equiv_refl := by
    intro h hh
    exact A.same_refl hh
  equiv_symm := by
    intro h k sameHK
    exact A.same_symm (A.same_left_carrier sameHK) (A.same_right_carrier sameHK) sameHK
  equiv_trans := by
    intro h k r sameHK sameKR
    exact A.same_trans (A.same_left_carrier sameHK)
      (A.same_right_carrier sameHK) (A.same_right_carrier sameKR) sameHK sameKR
  carrier_respects_equiv := by
    intro h k sameHK _hh
    exact A.same_right_carrier sameHK

def carrier_fin_data_iface (A : CarrierUp) (w : Hist) (hw : A.carrier w) :
    FinDataIface A where
  constr := { witness := w, witness_carrier := hw }
  elim := { expose := by intro h; intro hh; exact hh }
  stab := {
    hsame_transport := by
      intro h k sameHK hh
      exact A.carrier_hsame_transport sameHK hh
    same_refl_row := by
      intro h hh
      exact A.same_refl hh
  }
  ledger := {
    carrier_witness := ⟨w, hw⟩
    classifier_reflexive := by
      intro h hh
      exact A.same_refl hh
  }
  cert := carrier_name_cert A w hw

def BoolCarrier (h : Hist) : Prop :=
  hsame h emp \/ hsame h (Eone emp)

def BoolSame (h k : Hist) : Prop :=
  BoolCarrier h /\ BoolCarrier k /\ hsame h k

theorem bool_emp_carrier : BoolCarrier emp :=
  Or.inl (hsame_refl emp)

theorem bool_true_carrier : BoolCarrier (Eone emp) :=
  Or.inr (hsame_refl (Eone emp))

def bool_same_equiv : RelEquiv { h : Hist // BoolCarrier h } where
  rel x y := BoolSame x.1 y.1
  refl := by
    intro x
    exact ⟨x.2, x.2, hsame_refl x.1⟩
  symm := by
    intro x y sameXY
    exact ⟨sameXY.right.left, sameXY.left, hsame_symm sameXY.right.right⟩
  trans := by
    intro x y z sameXY sameYZ
    exact ⟨sameXY.left, sameYZ.right.left,
      hsame_trans sameXY.right.right sameYZ.right.right⟩

def BoolCarrierUp : CarrierUp where
  carrier := BoolCarrier
  same := BoolSame
  same_equiv := bool_same_equiv
  same_left_carrier := by
    intro h k sameHK
    exact sameHK.left
  same_right_carrier := by
    intro h k sameHK
    exact sameHK.right.left
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def bool_name_cert : NameCert BoolCarrier BoolSame :=
  carrier_name_cert BoolCarrierUp emp bool_emp_carrier

def BoolFinDataIface : FinDataIface BoolCarrierUp :=
  carrier_fin_data_iface BoolCarrierUp emp bool_emp_carrier

theorem bool_false_true_separated : ¬ BoolSame emp (Eone emp) := by
  intro sameFT
  exact not_hsame_emp_e1 sameFT.right.right

theorem bool_cases {h : Hist} :
    BoolCarrier h -> BoolSame h emp \/ BoolSame h (Eone emp) := by
  intro hh
  cases hh with
  | inl falseCase =>
      exact Or.inl ⟨Or.inl falseCase, bool_emp_carrier, falseCase⟩
  | inr trueCase =>
      exact Or.inr ⟨Or.inr trueCase, bool_true_carrier, trueCase⟩

def optionNone : Hist := Ezero emp
def optionSome (a : Hist) : Hist := Eone a

def OptionCarrier (A : CarrierUp) (h : Hist) : Prop :=
  hsame h optionNone \/ exists a : Hist, A.carrier a /\ hsame h (optionSome a)

def OptionSame (A : CarrierUp) (h k : Hist) : Prop :=
  (hsame h optionNone /\ hsame k optionNone) \/
    exists a : Hist, exists b : Hist,
      A.carrier a /\ A.carrier b /\ A.same a b /\
        hsame h (optionSome a) /\ hsame k (optionSome b)

theorem option_none_carrier (A : CarrierUp) :
    OptionCarrier A optionNone :=
  Or.inl (hsame_refl optionNone)

theorem option_some_carrier (A : CarrierUp) {a : Hist} :
    A.carrier a -> OptionCarrier A (optionSome a) := by
  intro ha
  exact Or.inr ⟨a, ha, hsame_refl (optionSome a)⟩

private theorem option_same_refl (A : CarrierUp) {h : Hist} :
    OptionCarrier A h -> OptionSame A h h := by
  intro hh
  cases hh with
  | inl hNone =>
      exact Or.inl ⟨hNone, hNone⟩
  | inr some =>
      cases some with
      | intro a data =>
          exact Or.inr ⟨a, a, data.left, data.left,
            A.same_refl data.left, data.right, data.right⟩

private theorem option_same_symm (A : CarrierUp) {h k : Hist} :
    OptionSame A h k -> OptionSame A k h := by
  intro sameHK
  cases sameHK with
  | inl noneCase =>
      exact Or.inl ⟨noneCase.right, noneCase.left⟩
  | inr someCase =>
      cases someCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inr ⟨b, a, data.right.left,
                data.left, A.same_symm data.left data.right.left data.right.right.left,
                data.right.right.right.right, data.right.right.right.left⟩

private theorem option_same_trans (A : CarrierUp) {h k r : Hist} :
    OptionSame A h k -> OptionSame A k r -> OptionSame A h r := by
  intro sameHK sameKR
  cases sameHK with
  | inl noneHK =>
      cases sameKR with
      | inl noneKR =>
          exact Or.inl ⟨noneHK.left, noneKR.right⟩
      | inr someKR =>
          cases someKR with
          | intro c rest =>
              cases rest with
              | intro d data =>
                  have conflict : hsame optionNone (optionSome c) :=
                    hsame_trans (hsame_symm noneHK.right) data.right.right.right.left
                  exact False.elim (not_hsame_e0_e1 conflict)
  | inr someHK =>
      cases someHK with
      | intro a restHK =>
          cases restHK with
          | intro b dataHK =>
              cases sameKR with
              | inl noneKR =>
                  have conflict : hsame optionNone (optionSome b) :=
                    hsame_trans (hsame_symm noneKR.left) dataHK.right.right.right.right
                  exact False.elim (not_hsame_e0_e1 conflict)
              | inr someKR =>
                  cases someKR with
                  | intro c restKR =>
                      cases restKR with
                      | intro d dataKR =>
                          have sameBCHist : hsame b c :=
                            hsame_e1_iff.mp
                              (hsame_trans
                                (hsame_symm dataHK.right.right.right.right)
                                dataKR.right.right.right.left)
                          have sameBC : A.same b c :=
                            A.same_of_hsame dataHK.right.left dataKR.left sameBCHist
                          have sameAC : A.same a c :=
                            A.same_trans dataHK.left dataHK.right.left dataKR.left
                              dataHK.right.right.left sameBC
                          have sameAD : A.same a d :=
                            A.same_trans dataHK.left dataKR.left dataKR.right.left
                              sameAC dataKR.right.right.left
                          exact Or.inr ⟨a, d, dataHK.left, dataKR.right.left,
                            sameAD, dataHK.right.right.right.left,
                            dataKR.right.right.right.right⟩

private theorem option_same_left_carrier (A : CarrierUp) {h k : Hist} :
    OptionSame A h k -> OptionCarrier A h := by
  intro sameHK
  cases sameHK with
  | inl noneCase =>
      exact Or.inl noneCase.left
  | inr someCase =>
      cases someCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inr ⟨a, data.left, data.right.right.right.left⟩

private theorem option_same_right_carrier (A : CarrierUp) {h k : Hist} :
    OptionSame A h k -> OptionCarrier A k := by
  intro sameHK
  cases sameHK with
  | inl noneCase =>
      exact Or.inl noneCase.right
  | inr someCase =>
      cases someCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inr ⟨b, data.right.left, data.right.right.right.right⟩

def option_same_equiv (A : CarrierUp) :
    RelEquiv { h : Hist // OptionCarrier A h } where
  rel x y := OptionSame A x.1 y.1
  refl := by
    intro x
    exact option_same_refl A x.2
  symm := by
    intro x y sameXY
    exact option_same_symm A sameXY
  trans := by
    intro x y z sameXY sameYZ
    exact option_same_trans A sameXY sameYZ

def OptionCarrierUp (A : CarrierUp) : CarrierUp where
  carrier := OptionCarrier A
  same := OptionSame A
  same_equiv := option_same_equiv A
  same_left_carrier := by
    intro h k sameHK
    exact option_same_left_carrier A sameHK
  same_right_carrier := by
    intro h k sameHK
    exact option_same_right_carrier A sameHK
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def OptionFinDataIface (A : CarrierUp) : FinDataIface (OptionCarrierUp A) :=
  carrier_fin_data_iface (OptionCarrierUp A) optionNone (option_none_carrier A)

theorem option_none_some_separated (A : CarrierUp) {a : Hist} :
    A.carrier a -> ¬ OptionSame A optionNone (optionSome a) := by
  intro _ha sameNS
  cases sameNS with
  | inl noneCase =>
      exact not_hsame_e0_e1
        (hsame_trans noneCase.left (hsame_symm noneCase.right))
  | inr someCase =>
      cases someCase with
      | intro b rest =>
          cases rest with
          | intro c data =>
              exact not_hsame_e0_e1 data.right.right.right.left

theorem option_payload_determinacy (A : CarrierUp) {a b : Hist} :
    A.carrier a -> A.carrier b ->
      OptionSame A (optionSome a) (optionSome b) -> A.same a b := by
  intro ha hb sameAB
  cases sameAB with
  | inl noneCase =>
      exact False.elim (not_hsame_e1_e0 noneCase.left)
  | inr someCase =>
      cases someCase with
      | intro a0 rest =>
          cases rest with
          | intro b0 data =>
              have sameAA0Hist : hsame a a0 :=
                hsame_e1_iff.mp data.right.right.right.left
              have sameBB0Hist : hsame b b0 :=
                hsame_e1_iff.mp data.right.right.right.right
              have sameAA0 : A.same a a0 :=
                A.same_of_hsame ha data.left sameAA0Hist
              have sameB0B : A.same b0 b :=
                A.same_symm hb data.right.left
                  (A.same_of_hsame hb data.right.left sameBB0Hist)
              exact A.same_trans ha data.left hb sameAA0
                (A.same_trans data.left data.right.left hb
                  data.right.right.left sameB0B)

def sumInl (a : Hist) : Hist := Ezero a
def sumInr (b : Hist) : Hist := Eone b

def SumCarrier (L R : CarrierUp) (h : Hist) : Prop :=
  (exists a : Hist, L.carrier a /\ hsame h (sumInl a)) \/
    exists b : Hist, R.carrier b /\ hsame h (sumInr b)

def SumSame (L R : CarrierUp) (h k : Hist) : Prop :=
  (exists a : Hist, exists b : Hist,
    L.carrier a /\ L.carrier b /\ L.same a b /\
      hsame h (sumInl a) /\ hsame k (sumInl b)) \/
    exists a : Hist, exists b : Hist,
      R.carrier a /\ R.carrier b /\ R.same a b /\
        hsame h (sumInr a) /\ hsame k (sumInr b)

private theorem sum_same_refl (L R : CarrierUp) {h : Hist} :
    SumCarrier L R h -> SumSame L R h h := by
  intro hh
  cases hh with
  | inl leftCase =>
      cases leftCase with
      | intro a data =>
          exact Or.inl ⟨a, a, data.left, data.left,
            L.same_refl data.left, data.right, data.right⟩
  | inr rightCase =>
      cases rightCase with
      | intro b data =>
          exact Or.inr ⟨b, b, data.left, data.left,
            R.same_refl data.left, data.right, data.right⟩

private theorem sum_same_symm (L R : CarrierUp) {h k : Hist} :
    SumSame L R h k -> SumSame L R k h := by
  intro sameHK
  cases sameHK with
  | inl leftCase =>
      cases leftCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inl ⟨b, a, data.right.left, data.left,
                L.same_symm data.left data.right.left data.right.right.left,
                data.right.right.right.right, data.right.right.right.left⟩
  | inr rightCase =>
      cases rightCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inr ⟨b, a, data.right.left, data.left,
                R.same_symm data.left data.right.left data.right.right.left,
                data.right.right.right.right, data.right.right.right.left⟩

private theorem sum_same_trans (L R : CarrierUp) {h k r : Hist} :
    SumSame L R h k -> SumSame L R k r -> SumSame L R h r := by
  intro sameHK sameKR
  cases sameHK with
  | inl leftHK =>
      cases leftHK with
      | intro a restHK =>
          cases restHK with
          | intro b dataHK =>
              cases sameKR with
              | inl leftKR =>
                  cases leftKR with
                  | intro c restKR =>
                      cases restKR with
                      | intro d dataKR =>
                          have sameBCHist : hsame b c :=
                            hsame_e0_iff.mp
                              (hsame_trans
                                (hsame_symm dataHK.right.right.right.right)
                                dataKR.right.right.right.left)
                          have sameBC : L.same b c :=
                            L.same_of_hsame dataHK.right.left dataKR.left sameBCHist
                          have sameAC : L.same a c :=
                            L.same_trans dataHK.left dataHK.right.left dataKR.left
                              dataHK.right.right.left sameBC
                          have sameAD : L.same a d :=
                            L.same_trans dataHK.left dataKR.left dataKR.right.left
                              sameAC dataKR.right.right.left
                          exact Or.inl ⟨a, d, dataHK.left, dataKR.right.left,
                            sameAD, dataHK.right.right.right.left,
                            dataKR.right.right.right.right⟩
              | inr rightKR =>
                  cases rightKR with
                  | intro c restKR =>
                      cases restKR with
                      | intro d dataKR =>
                          have conflict : hsame (sumInl b) (sumInr c) :=
                            hsame_trans
                              (hsame_symm dataHK.right.right.right.right)
                              dataKR.right.right.right.left
                          exact False.elim (not_hsame_e0_e1 conflict)
  | inr rightHK =>
      cases rightHK with
      | intro a restHK =>
          cases restHK with
          | intro b dataHK =>
              cases sameKR with
              | inl leftKR =>
                  cases leftKR with
                  | intro c restKR =>
                      cases restKR with
                      | intro d dataKR =>
                          have conflict : hsame (sumInl c) (sumInr b) :=
                            hsame_trans
                              (hsame_symm dataKR.right.right.right.left)
                              dataHK.right.right.right.right
                          exact False.elim (not_hsame_e0_e1 conflict)
              | inr rightKR =>
                  cases rightKR with
                  | intro c restKR =>
                      cases restKR with
                      | intro d dataKR =>
                          have sameBCHist : hsame b c :=
                            hsame_e1_iff.mp
                              (hsame_trans
                                (hsame_symm dataHK.right.right.right.right)
                                dataKR.right.right.right.left)
                          have sameBC : R.same b c :=
                            R.same_of_hsame dataHK.right.left dataKR.left sameBCHist
                          have sameAC : R.same a c :=
                            R.same_trans dataHK.left dataHK.right.left dataKR.left
                              dataHK.right.right.left sameBC
                          have sameAD : R.same a d :=
                            R.same_trans dataHK.left dataKR.left dataKR.right.left
                              sameAC dataKR.right.right.left
                          exact Or.inr ⟨a, d, dataHK.left, dataKR.right.left,
                            sameAD, dataHK.right.right.right.left,
                            dataKR.right.right.right.right⟩

private theorem sum_same_left_carrier (L R : CarrierUp) {h k : Hist} :
    SumSame L R h k -> SumCarrier L R h := by
  intro sameHK
  cases sameHK with
  | inl leftCase =>
      cases leftCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inl ⟨a, data.left, data.right.right.right.left⟩
  | inr rightCase =>
      cases rightCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inr ⟨a, data.left, data.right.right.right.left⟩

private theorem sum_same_right_carrier (L R : CarrierUp) {h k : Hist} :
    SumSame L R h k -> SumCarrier L R k := by
  intro sameHK
  cases sameHK with
  | inl leftCase =>
      cases leftCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inl ⟨b, data.right.left, data.right.right.right.right⟩
  | inr rightCase =>
      cases rightCase with
      | intro a rest =>
          cases rest with
          | intro b data =>
              exact Or.inr ⟨b, data.right.left, data.right.right.right.right⟩

def sum_same_equiv (L R : CarrierUp) :
    RelEquiv { h : Hist // SumCarrier L R h } where
  rel x y := SumSame L R x.1 y.1
  refl := by
    intro x
    exact sum_same_refl L R x.2
  symm := by
    intro x y sameXY
    exact sum_same_symm L R sameXY
  trans := by
    intro x y z sameXY sameYZ
    exact sum_same_trans L R sameXY sameYZ

def SumCarrierUp (L R : CarrierUp) : CarrierUp where
  carrier := SumCarrier L R
  same := SumSame L R
  same_equiv := sum_same_equiv L R
  same_left_carrier := by
    intro h k sameHK
    exact sum_same_left_carrier L R sameHK
  same_right_carrier := by
    intro h k sameHK
    exact sum_same_right_carrier L R sameHK
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def SumFinDataIfaceLeft (L R : CarrierUp) (I : FinDataIface L) :
    FinDataIface (SumCarrierUp L R) :=
  carrier_fin_data_iface (SumCarrierUp L R)
    (sumInl I.constr.witness)
    (Or.inl ⟨I.constr.witness, I.constr.witness_carrier,
      hsame_refl (sumInl I.constr.witness)⟩)

theorem sum_inl_inr_separated (L R : CarrierUp) {a b : Hist} :
    L.carrier a -> R.carrier b -> ¬ SumSame L R (sumInl a) (sumInr b) := by
  intro _ha _hb sameLR
  cases sameLR with
  | inl leftCase =>
      cases leftCase with
      | intro a0 rest =>
          cases rest with
          | intro b0 data =>
              exact not_hsame_e1_e0 data.right.right.right.right
  | inr rightCase =>
      cases rightCase with
      | intro a0 rest =>
          cases rest with
          | intro b0 data =>
              exact not_hsame_e0_e1 data.right.right.right.left

def prodPairCode (l r : Hist) : Hist :=
  append (Ezero l) (Eone r)

structure ProdPairRep (L R : CarrierUp) (h l r : Hist) : Prop where
  left_carrier : L.carrier l
  right_carrier : R.carrier r
  pair_cont : ContR (Ezero l) (Eone r) h

def ProdCarrier (L R : CarrierUp) (h : Hist) : Prop :=
  exists l : Hist, exists r : Hist, ProdPairRep L R h l r

def ProdSame (L R : CarrierUp) (h k : Hist) : Prop :=
  ProdCarrier L R h /\ ProdCarrier L R k /\ hsame h k

def ProdCarrierUp (L R : CarrierUp) : CarrierUp where
  carrier := ProdCarrier L R
  same := ProdSame L R
  same_equiv := {
    rel := fun x y => ProdSame L R x.1 y.1
    refl := by
      intro x
      exact ⟨x.2, x.2, hsame_refl x.1⟩
    symm := by
      intro x y sameXY
      exact ⟨sameXY.right.left, sameXY.left, hsame_symm sameXY.right.right⟩
    trans := by
      intro x y z sameXY sameYZ
      exact ⟨sameXY.left, sameYZ.right.left,
        hsame_trans sameXY.right.right sameYZ.right.right⟩
  }
  same_left_carrier := by
    intro h k sameHK
    exact sameHK.left
  same_right_carrier := by
    intro h k sameHK
    exact sameHK.right.left
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def ProdFinDataIface (L R : CarrierUp)
    (IL : FinDataIface L) (IR : FinDataIface R) :
    FinDataIface (ProdCarrierUp L R) :=
  carrier_fin_data_iface (ProdCarrierUp L R)
    (prodPairCode IL.constr.witness IR.constr.witness)
    ⟨IL.constr.witness, IR.constr.witness,
      {
        left_carrier := IL.constr.witness_carrier
        right_carrier := IR.constr.witness_carrier
        pair_cont := rfl
      }⟩

theorem prod_classifier_exposes_ledgers (L R : CarrierUp) {h k : Hist} :
    ProdSame L R h k ->
      (exists l : Hist, exists r : Hist, ProdPairRep L R h l r) /\
        (exists l : Hist, exists r : Hist, ProdPairRep L R k l r) := by
  intro sameHK
  exact ⟨sameHK.left, sameHK.right.left⟩

inductive ListSpine (A : CarrierUp) : Type where
  | nil : ListSpine A
  | cons (a : Hist) (ha : A.carrier a) (tail : ListSpine A) : ListSpine A

namespace ListSpine

def code {A : CarrierUp} : ListSpine A -> Hist
  | nil => Ezero emp
  | cons a _ha tail => Eone (append a (code tail))

end ListSpine

inductive ListSpineSame (A : CarrierUp) : ListSpine A -> ListSpine A -> Prop where
  | nil : ListSpineSame A ListSpine.nil ListSpine.nil
  | cons {a b : Hist} {ha : A.carrier a} {hb : A.carrier b}
      {xs ys : ListSpine A} :
      A.same a b -> ListSpineSame A xs ys ->
        ListSpineSame A (ListSpine.cons a ha xs) (ListSpine.cons b hb ys)

def ListCarrier (A : CarrierUp) (h : Hist) : Prop :=
  exists xs : ListSpine A, hsame h (ListSpine.code xs)

def ListSame (A : CarrierUp) (h k : Hist) : Prop :=
  ListCarrier A h /\ ListCarrier A k /\ hsame h k

def ListCarrierUp (A : CarrierUp) : CarrierUp where
  carrier := ListCarrier A
  same := ListSame A
  same_equiv := {
    rel := fun x y => ListSame A x.1 y.1
    refl := by
      intro x
      exact ⟨x.2, x.2, hsame_refl x.1⟩
    symm := by
      intro x y sameXY
      exact ⟨sameXY.right.left, sameXY.left, hsame_symm sameXY.right.right⟩
    trans := by
      intro x y z sameXY sameYZ
      exact ⟨sameXY.left, sameYZ.right.left,
        hsame_trans sameXY.right.right sameYZ.right.right⟩
  }
  same_left_carrier := by
    intro h k sameHK
    exact sameHK.left
  same_right_carrier := by
    intro h k sameHK
    exact sameHK.right.left
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def ListFinDataIface (A : CarrierUp) : FinDataIface (ListCarrierUp A) :=
  carrier_fin_data_iface (ListCarrierUp A)
    (ListSpine.code (A := A) ListSpine.nil)
    ⟨ListSpine.nil, hsame_refl (ListSpine.code (A := A) ListSpine.nil)⟩

def ListFoldUp (A : CarrierUp) {M : Type u}
    (nilValue : M)
    (consStep : (a : Hist) -> A.carrier a -> M -> M) :
    ListSpine A -> M
  | ListSpine.nil => nilValue
  | ListSpine.cons a ha tail => consStep a ha (ListFoldUp A nilValue consStep tail)

theorem list_induction_up (A : CarrierUp) {P : ListSpine A -> Prop}
    (nil_case : P ListSpine.nil)
    (cons_case :
      forall (a : Hist) (ha : A.carrier a) (tail : ListSpine A),
        P tail -> P (ListSpine.cons a ha tail)) :
    forall xs : ListSpine A, P xs := by
  intro xs
  induction xs with
  | nil =>
      exact nil_case
  | cons a ha tail ih =>
      exact cons_case a ha tail ih

theorem list_fold_congr (A : CarrierUp) {M : Type u}
    {R : M -> M -> Prop}
    {nilValue : M}
    {consStep : (a : Hist) -> A.carrier a -> M -> M}
    (nil_rel : R nilValue nilValue)
    (cons_rel :
      forall {a b : Hist} {ha : A.carrier a} {hb : A.carrier b}
        {x y : M},
        A.same a b -> R x y ->
          R (consStep a ha x) (consStep b hb y)) :
    forall {xs ys : ListSpine A},
      ListSpineSame A xs ys ->
        R (ListFoldUp A nilValue consStep xs)
          (ListFoldUp A nilValue consStep ys) := by
  intro xs ys sameXS
  induction sameXS with
  | nil =>
      exact nil_rel
  | cons headSame tailSame ih =>
      exact cons_rel headSame ih

end BEDC.Algebra.Spine.FiniteData
