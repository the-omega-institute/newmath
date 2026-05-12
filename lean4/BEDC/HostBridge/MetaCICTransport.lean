import BEDC.MetaCIC.TypedExamples.Identity
import BEDC.MetaCIC.TypedExamples.Polymorphic
import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.BetaRedex

namespace BEDC.HostBridge.MetaCICTransport

abbrev MetaTerm := BEDC.MetaCIC.Term

namespace Host

def identity : (X : Type) → X → X :=
  fun _ x => x

def const : (A B : Type) → A → B → A :=
  fun _ _ a _ => a

def flip : (A B C : Type) → (A → B → C) → B → A → C :=
  fun _ _ _ f b a => f a b

def compose : (A B C : Type) → (B → C) → (A → B) → A → C :=
  fun _ _ _ g f a => g (f a)

def churchBool : Type 1 :=
  (X : Type) → X → X → X

def churchTrue : churchBool :=
  fun _ t _ => t

def churchFalse : churchBool :=
  fun _ _ f => f

def churchNat : Type 1 :=
  (X : Type) → (X → X) → X → X

def churchZero : churchNat :=
  fun _ _ z => z

def churchOne : churchNat :=
  fun _ s z => s z

def churchSucc : churchNat → churchNat :=
  fun n X s z => s (n X s z)

def churchPair (A B : Type) : Type 1 :=
  (X : Type) → (A → B → X) → X

def churchMkPair : (A B : Type) → A → B → churchPair A B :=
  fun _ _ a b _ k => k a b

def churchFst : (A B : Type) → churchPair A B → A :=
  fun A B p => p A (fun a (_ : B) => a)

def churchSnd : (A B : Type) → churchPair A B → B :=
  fun A B p => p B (fun (_ : A) b => b)

def churchOption (A : Type) : Type 1 :=
  (X : Type) → X → (A → X) → X

def churchNone : (A : Type) → churchOption A :=
  fun _ _ n _ => n

def churchSome : (A : Type) → A → churchOption A :=
  fun _ a _ _ s => s a

def churchCaseOption :
    (A X : Type) → churchOption A → X → (A → X) → X :=
  fun _ _ o n s => o _ n s

def idSortRedex : Type 1 :=
  (fun X : Type 1 => X) Type

def fnSortToSortRedex : Type 1 :=
  (fun X : Type 1 => X → X) Type

def constSortRedex : Type 1 :=
  (fun _ : Type 1 => Type) Type

def innerSortIdRedex : Type → Type :=
  fun X => (fun Y : Type => Y) X

def appRightIdSortRedex : Type 1 :=
  (fun _ : Type 1 => Type) ((fun X : Type 1 => X) Type)

def polyIdTwoStepRedex : Type 1 :=
  (fun (X : Type 2) (x : X) => x) (Type 1) Type

def kSortTwoStepRedex : Type 1 :=
  (fun (X : Type 1) (_ : Type 1) => X) Type Type

theorem host_identity_beta (X : Type) (x : X) :
    identity X x = x := by
  rfl

theorem host_const_beta (A B : Type) (a : A) (b : B) :
    const A B a b = a := by
  rfl

theorem host_flip_beta (A B C : Type) (f : A → B → C) (b : B) (a : A) :
    flip A B C f b a = f a b := by
  rfl

theorem host_compose_beta
    (A B C : Type) (g : B → C) (f : A → B) (a : A) :
    compose A B C g f a = g (f a) := by
  rfl

theorem host_church_true_beta (X : Type) (t f : X) :
    churchTrue X t f = t := by
  rfl

theorem host_church_false_beta (X : Type) (t f : X) :
    churchFalse X t f = f := by
  rfl

theorem host_church_zero_beta (X : Type) (s : X → X) (z : X) :
    churchZero X s z = z := by
  rfl

theorem host_church_one_beta (X : Type) (s : X → X) (z : X) :
    churchOne X s z = s z := by
  rfl

theorem host_church_succ_beta
    (n : churchNat) (X : Type) (s : X → X) (z : X) :
    churchSucc n X s z = s (n X s z) := by
  rfl

theorem host_pair_fst_beta (A B : Type) (a : A) (b : B) :
    churchFst A B (churchMkPair A B a b) = a := by
  rfl

theorem host_pair_snd_beta (A B : Type) (a : A) (b : B) :
    churchSnd A B (churchMkPair A B a b) = b := by
  rfl

theorem host_none_beta (A X : Type) (n : X) (s : A → X) :
    churchCaseOption A X (churchNone A) n s = n := by
  rfl

theorem host_some_beta (A X : Type) (a : A) (n : X) (s : A → X) :
    churchCaseOption A X (churchSome A a) n s = s a := by
  rfl

theorem host_id_sort_redex_nf :
    idSortRedex = Type := by
  rfl

theorem host_fn_sort_to_sort_redex_nf :
    fnSortToSortRedex = (Type → Type) := by
  rfl

theorem host_const_sort_redex_nf :
    constSortRedex = Type := by
  rfl

theorem host_inner_sort_id_redex_nf :
    innerSortIdRedex = (fun X : Type => X) := by
  rfl

theorem host_app_right_id_sort_redex_nf :
    appRightIdSortRedex = Type := by
  rfl

theorem host_poly_id_two_step_redex_nf :
    polyIdTwoStepRedex = Type := by
  rfl

theorem host_k_sort_two_step_redex_nf :
    kSortTwoStepRedex = Type := by
  rfl

end Host

namespace Meta

abbrev identity : MetaTerm :=
  BEDC.MetaCIC.churchIdentityTm

abbrev identityTy : MetaTerm :=
  BEDC.MetaCIC.churchIdentityTy

abbrev const : MetaTerm :=
  BEDC.MetaCIC.churchConstTm

abbrev constTy : MetaTerm :=
  BEDC.MetaCIC.churchConstTy

abbrev flip : MetaTerm :=
  BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
    (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
      (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.lam
          (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 2)
            (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 2)
              (BEDC.MetaCIC.Term.var 2)))
          (BEDC.MetaCIC.Term.lam (BEDC.MetaCIC.Term.var 2)
            (BEDC.MetaCIC.Term.lam (BEDC.MetaCIC.Term.var 4)
              (BEDC.MetaCIC.Term.app
                (BEDC.MetaCIC.Term.app (BEDC.MetaCIC.Term.var 2)
                  (BEDC.MetaCIC.Term.var 0))
                (BEDC.MetaCIC.Term.var 1)))))))

abbrev flipTy : MetaTerm :=
  BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort
    (BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort
      (BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.pi
          (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 2)
            (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 2)
              (BEDC.MetaCIC.Term.var 2)))
          (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 2)
            (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 4)
              (BEDC.MetaCIC.Term.var 3))))))

abbrev compose : MetaTerm :=
  BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
    (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
      (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.lam
          (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 1)
            (BEDC.MetaCIC.Term.var 1))
          (BEDC.MetaCIC.Term.lam
            (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 3)
              (BEDC.MetaCIC.Term.var 3))
            (BEDC.MetaCIC.Term.lam (BEDC.MetaCIC.Term.var 4)
              (BEDC.MetaCIC.Term.app (BEDC.MetaCIC.Term.var 2)
                (BEDC.MetaCIC.Term.app (BEDC.MetaCIC.Term.var 1)
                  (BEDC.MetaCIC.Term.var 0))))))))

abbrev composeTy : MetaTerm :=
  BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort
    (BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort
      (BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.pi
          (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 1)
            (BEDC.MetaCIC.Term.var 1))
          (BEDC.MetaCIC.Term.pi
            (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 3)
              (BEDC.MetaCIC.Term.var 3))
            (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 4)
              (BEDC.MetaCIC.Term.var 3))))))

abbrev churchBoolTy : MetaTerm :=
  BEDC.MetaCIC.churchBoolTy

abbrev churchTrue : MetaTerm :=
  BEDC.MetaCIC.churchTrueTm

abbrev churchFalse : MetaTerm :=
  BEDC.MetaCIC.churchFalseTm

abbrev churchNatTy : MetaTerm :=
  BEDC.MetaCIC.churchNatTy

abbrev churchZero : MetaTerm :=
  BEDC.MetaCIC.churchZeroTm

abbrev churchOne : MetaTerm :=
  BEDC.MetaCIC.churchOneTm

abbrev churchSucc : MetaTerm :=
  BEDC.MetaCIC.churchSuccTm

abbrev churchSuccTy : MetaTerm :=
  BEDC.MetaCIC.churchSuccTy

abbrev churchPairTy : MetaTerm :=
  BEDC.MetaCIC.churchPairTy

abbrev churchMkPair : MetaTerm :=
  BEDC.MetaCIC.churchMkPairTm

abbrev churchMkPairTy : MetaTerm :=
  BEDC.MetaCIC.churchMkPairTy

abbrev churchFst : MetaTerm :=
  BEDC.MetaCIC.churchFstTm

abbrev churchFstTy : MetaTerm :=
  BEDC.MetaCIC.churchFstTy

abbrev churchSnd : MetaTerm :=
  BEDC.MetaCIC.churchSndTm

abbrev churchSndTy : MetaTerm :=
  BEDC.MetaCIC.churchSndTy

abbrev churchOptionTy : MetaTerm :=
  BEDC.MetaCIC.churchOptionTy

abbrev churchNone : MetaTerm :=
  BEDC.MetaCIC.churchNoneTm

abbrev churchNoneTy : MetaTerm :=
  BEDC.MetaCIC.churchNoneTy

abbrev churchSome : MetaTerm :=
  BEDC.MetaCIC.churchSomeTm

abbrev churchSomeTy : MetaTerm :=
  BEDC.MetaCIC.churchSomeTy

abbrev idSortRedex : MetaTerm :=
  BEDC.MetaCIC.Term.app
    (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort (BEDC.MetaCIC.Term.var 0))
    BEDC.MetaCIC.Term.sort

abbrev fnSortToSortRedex : MetaTerm :=
  BEDC.MetaCIC.Term.app
    (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
      (BEDC.MetaCIC.Term.pi (BEDC.MetaCIC.Term.var 0)
        (BEDC.MetaCIC.Term.var 1)))
    BEDC.MetaCIC.Term.sort

abbrev constSortRedex : MetaTerm :=
  BEDC.MetaCIC.Term.app
    (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort BEDC.MetaCIC.Term.sort)
    BEDC.MetaCIC.Term.sort

abbrev innerSortIdRedex : MetaTerm :=
  BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
    (BEDC.MetaCIC.Term.app
      (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.var 0))
      (BEDC.MetaCIC.Term.var 0))

abbrev appRightIdSortRedex : MetaTerm :=
  BEDC.MetaCIC.Term.app
    (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort BEDC.MetaCIC.Term.sort)
    idSortRedex

abbrev polyIdTwoStepRedex : MetaTerm :=
  BEDC.MetaCIC.Term.app
    (BEDC.MetaCIC.Term.app
      (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.lam (BEDC.MetaCIC.Term.var 0)
          (BEDC.MetaCIC.Term.var 0)))
      BEDC.MetaCIC.Term.sort)
    BEDC.MetaCIC.Term.sort

abbrev kSortTwoStepRedex : MetaTerm :=
  BEDC.MetaCIC.Term.app
    (BEDC.MetaCIC.Term.app
      (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
          (BEDC.MetaCIC.Term.var 1)))
      BEDC.MetaCIC.Term.sort)
    BEDC.MetaCIC.Term.sort

end Meta

theorem transport_identity_well_typed :
    BEDC.MetaCIC.HasType [] Meta.identity Meta.identityTy := by
  exact BEDC.MetaCIC.church_identity

theorem transport_const_well_typed :
    BEDC.MetaCIC.HasType [] Meta.const Meta.constTy := by
  exact BEDC.MetaCIC.church_const

theorem transport_flip_well_typed :
    BEDC.MetaCIC.HasType [] Meta.flip Meta.flipTy := by
  exact BEDC.MetaCIC.poly_flip_type

theorem transport_compose_well_typed :
    BEDC.MetaCIC.HasType [] Meta.compose Meta.composeTy := by
  exact BEDC.MetaCIC.poly_compose_type

theorem transport_church_bool_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchBoolTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_bool_type

theorem transport_church_true_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchTrue Meta.churchBoolTy := by
  exact BEDC.MetaCIC.church_true

theorem transport_church_false_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchFalse Meta.churchBoolTy := by
  exact BEDC.MetaCIC.church_false

theorem transport_church_nat_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchNatTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_nat_type

theorem transport_church_zero_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchZero Meta.churchNatTy := by
  exact BEDC.MetaCIC.church_zero

theorem transport_church_one_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchOne Meta.churchNatTy := by
  exact BEDC.MetaCIC.church_one

theorem transport_church_succ_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchSuccTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_succ_type

theorem transport_church_succ_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchSucc Meta.churchSuccTy := by
  exact BEDC.MetaCIC.church_succ

theorem transport_church_pair_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchPairTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_pair_type

theorem transport_church_mk_pair_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchMkPairTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_mk_pair_type

theorem transport_church_mk_pair_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchMkPair Meta.churchMkPairTy := by
  exact BEDC.MetaCIC.church_mk_pair

theorem transport_church_fst_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchFstTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_fst_type

theorem transport_church_fst_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchFst Meta.churchFstTy := by
  exact BEDC.MetaCIC.church_fst

theorem transport_church_snd_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchSndTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_snd_type

theorem transport_church_snd_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchSnd Meta.churchSndTy := by
  exact BEDC.MetaCIC.church_snd

theorem transport_church_option_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchOptionTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_option_type

theorem transport_church_none_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchNoneTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_none_type

theorem transport_church_none_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchNone Meta.churchNoneTy := by
  exact BEDC.MetaCIC.church_none

theorem transport_church_some_type_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchSomeTy BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.church_some_type

theorem transport_church_some_well_typed :
    BEDC.MetaCIC.HasType [] Meta.churchSome Meta.churchSomeTy := by
  exact BEDC.MetaCIC.church_some

theorem transport_id_sort_redex_step :
    BEDC.MetaCIC.BetaStep Meta.idSortRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.id_sort_redex

theorem transport_id_sort_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.idSortRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.id_sort_redex_typed

theorem transport_fn_sort_to_sort_redex_step :
    BEDC.MetaCIC.BetaStep Meta.fnSortToSortRedex
      (BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort BEDC.MetaCIC.Term.sort) := by
  exact BEDC.MetaCIC.fn_sort_to_sort_redex

theorem transport_fn_sort_to_sort_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.fnSortToSortRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.fn_sort_to_sort_redex_typed

theorem transport_const_sort_redex_step :
    BEDC.MetaCIC.BetaStep Meta.constSortRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.const_sort_redex

theorem transport_const_sort_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.constSortRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.const_sort_redex_typed

theorem transport_inner_sort_id_redex_step :
    BEDC.MetaCIC.BetaStep Meta.innerSortIdRedex
      (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort
        (BEDC.MetaCIC.Term.var 0)) := by
  exact BEDC.MetaCIC.inner_sort_id_redex

theorem transport_inner_sort_id_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.innerSortIdRedex
      (BEDC.MetaCIC.Term.pi BEDC.MetaCIC.Term.sort BEDC.MetaCIC.Term.sort) := by
  exact BEDC.MetaCIC.inner_sort_id_redex_typed

theorem transport_app_right_id_sort_redex_step :
    BEDC.MetaCIC.BetaStep Meta.appRightIdSortRedex
      (BEDC.MetaCIC.Term.app
        (BEDC.MetaCIC.Term.lam BEDC.MetaCIC.Term.sort BEDC.MetaCIC.Term.sort)
        BEDC.MetaCIC.Term.sort) := by
  exact BEDC.MetaCIC.app_right_id_sort_redex

theorem transport_app_right_id_sort_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.appRightIdSortRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.app_right_id_sort_redex_typed

theorem transport_poly_id_two_step_redex_star :
    BEDC.MetaCIC.BetaStarStep Meta.polyIdTwoStepRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.poly_id_two_step_redex

theorem transport_poly_id_two_step_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.polyIdTwoStepRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.poly_id_two_step_redex_typed

theorem transport_k_sort_two_step_redex_star :
    BEDC.MetaCIC.BetaStarStep Meta.kSortTwoStepRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.k_sort_two_step_redex

theorem transport_k_sort_two_step_redex_well_typed :
    BEDC.MetaCIC.HasType [] Meta.kSortTwoStepRedex BEDC.MetaCIC.Term.sort := by
  exact BEDC.MetaCIC.k_sort_two_step_redex_typed

end BEDC.HostBridge.MetaCICTransport
