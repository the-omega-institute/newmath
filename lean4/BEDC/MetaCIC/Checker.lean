import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

/-- de Bruijn index 的结构布尔相等。 -/
def idxBeq (i j : Idx) : Bool :=
  Nat.rec
    (motive := fun _ => Idx → Bool)
    (fun j =>
      @Nat.casesOn (motive := fun _ => Bool) j true (fun _ => false))
    (fun _ ih j =>
      @Nat.casesOn (motive := fun _ => Bool) j false (fun j' => ih j'))
    i j

/-- var 分支的二项比较, 用 casesOn 固定纯消去路径。 -/
def Term.beqVar (i : Idx) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun j => idxBeq i j)
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    false

/-- app 分支的二项比较。 -/
def Term.beqApp (bf ba : Term → Bool) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun f' a' => bf f' && ba a')
    (fun _ _ => false)
    (fun _ _ => false)
    false

/-- lam 分支的二项比较。 -/
def Term.beqLam (bd bb : Term → Bool) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun _ _ => false)
    (fun d' b' => bd d' && bb b')
    (fun _ _ => false)
    false

/-- pi 分支的二项比较。 -/
def Term.beqPi (bd bc : Term → Bool) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    (fun d' c' => bd d' && bc c')
    false

/-- sort 分支的二项比较。 -/
def Term.beqSort (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    true

/-- 比较两个 Term 是否结构相等。 -/
def Term.beq : Term → Term → Bool
  | Term.var i => Term.beqVar i
  | Term.app f a => Term.beqApp (Term.beq f) (Term.beq a)
  | Term.lam d b => Term.beqLam (Term.beq d) (Term.beq b)
  | Term.pi d c => Term.beqPi (Term.beq d) (Term.beq c)
  | Term.sort => Term.beqSort

theorem idxBeq_eq {i j : Idx} (h : idxBeq i j = true) : i = j := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => rfl
      | succ _ => cases h
  | succ i ih =>
      cases j with
      | zero => cases h
      | succ j =>
          cases ih h
          rfl

theorem bool_and_left_true : {a b : Bool} → (a && b) = true → a = true
  | false, _, h => nomatch h
  | true, _, _ => rfl

theorem bool_and_right_true : {a b : Bool} → (a && b) = true → b = true
  | false, _, h => nomatch h
  | true, _, h => h

theorem Term.beq_eq {x y : Term} (h : Term.beq x y = true) : x = y := by
  induction x generalizing y with
  | var i =>
      cases y with
      | var j =>
          cases idxBeq_eq h
          rfl
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi _ _ => cases h
      | sort => cases h
  | app f a ihf iha =>
      cases y with
      | var _ => cases h
      | app f' a' =>
          cases ihf (bool_and_left_true h)
          cases iha (bool_and_right_true h)
          rfl
      | lam _ _ => cases h
      | pi _ _ => cases h
      | sort => cases h
  | lam d b ihd ihb =>
      cases y with
      | var _ => cases h
      | app _ _ => cases h
      | lam d' b' =>
          cases ihd (bool_and_left_true h)
          cases ihb (bool_and_right_true h)
          rfl
      | pi _ _ => cases h
      | sort => cases h
  | pi d c ihd ihc =>
      cases y with
      | var _ => cases h
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi d' c' =>
          cases ihd (bool_and_left_true h)
          cases ihc (bool_and_right_true h)
          rfl
      | sort => cases h
  | sort =>
      cases y with
      | var _ => cases h
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi _ _ => cases h
      | sort => rfl

theorem bool_if_some_true {b : Bool} {X A : Term}
    (h : (if b then some X else none) = some A) : b = true := by
  cases b with
  | false => cases h
  | true => rfl

theorem bool_if_some_value {b : Bool} {X A : Term}
    (h : (if b then some X else none) = some A) : X = A := by
  cases b with
  | false => cases h
  | true =>
      cases h
      rfl

theorem bool_eq_true_false_absurd {b : Bool} (hb : b = false) (h : b = true) :
    False := by
  cases hb
  cases h

def inferPi (codInf domInf : Option Term) : Option Term :=
  @Option.casesOn (α := Term) (motive := fun _ => Option Term) domInf none
    (fun dTy =>
      @Term.casesOn (motive := fun _ => Option Term) dTy
        (fun _ => none)
        (fun _ _ => none)
        (fun _ _ => none)
        (fun _ _ => none)
        (@Option.casesOn (α := Term) (motive := fun _ => Option Term) codInf none
          (fun cTy =>
            @Term.casesOn (motive := fun _ => Option Term) cTy
              (fun _ => none)
              (fun _ _ => none)
              (fun _ _ => none)
              (fun _ _ => none)
              (some Term.sort))))

def inferLam (bodyInf domInf : Option Term) (dom : Term) : Option Term :=
  @Option.casesOn (α := Term) (motive := fun _ => Option Term) domInf none
    (fun dTy =>
      @Term.casesOn (motive := fun _ => Option Term) dTy
        (fun _ => none)
        (fun _ _ => none)
        (fun _ _ => none)
        (fun _ _ => none)
        (@Option.casesOn (α := Term) (motive := fun _ => Option Term) bodyInf none
          (fun bodyTy => some (Term.pi dom bodyTy))))

def inferAppArg (aInf : Option Term) (a dom cod : Term) : Option Term :=
  match aInf with
  | none => none
  | some aTy =>
      match Term.beq aTy dom with
      | true => some (substitute 0 a cod)
      | false => none

def inferApp (aInf fInf : Option Term) (a : Term) : Option Term :=
  @Option.casesOn (α := Term) (motive := fun _ => Option Term) fInf none
    (fun fTy =>
      @Term.casesOn (motive := fun _ => Option Term) fTy
        (fun _ => none)
        (fun _ _ => none)
        (fun _ _ => none)
        (fun dom cod => inferAppArg aInf a dom cod)
        none)

/-- Recursive checker. 返回 some (推断的类型) 或 none。 -/
def infer : Ctx → Term → Option Term
  | _, Term.sort => some Term.sort
  | Γ, Term.var i =>
      Γ.lookup i
  | Γ, Term.pi dom cod =>
      inferPi (infer (dom :: Γ) cod) (infer Γ dom)
  | Γ, Term.lam dom body =>
      inferLam (infer (dom :: Γ) body) (infer Γ dom) dom
  | Γ, Term.app f a =>
      inferApp (infer Γ a) (infer Γ f) a

inductive InferHas (Γ : Ctx) (t : Term) : Option Term → Prop
  | noneIntro : InferHas Γ t none
  | someIntro (A : Term) : HasType Γ t A → InferHas Γ t (some A)

theorem InferHas.some_has {Γ : Ctx} {t A : Term} {opt : Option Term}
    (hopt : InferHas Γ t opt) (h : opt = some A) :
    HasType Γ t A :=
  match hopt with
  | InferHas.noneIntro => nomatch h
  | InferHas.someIntro _ hty =>
      match h with
      | rfl => hty

theorem InferHas.app_if {Γ : Ctx} {f a dom cod aTy : Term}
    (hf : HasType Γ f (Term.pi dom cod))
    (ha : HasType Γ a aTy) :
    InferHas Γ (Term.app f a)
      (match Term.beq aTy dom with
      | true => some (substitute 0 a cod)
      | false => none) := by
  cases hb : Term.beq aTy dom with
  | false =>
      exact InferHas.noneIntro
  | true =>
      match Term.beq_eq hb with
      | rfl =>
          exact InferHas.someIntro (substitute 0 a cod)
            (HasType.appRule Γ f a aTy cod hf ha)

theorem InferHas.app {Γ : Ctx} {f a : Term}
    (fInf aInf : Option Term)
    (hf : InferHas Γ f fInf)
    (ha : InferHas Γ a aInf) :
    InferHas Γ (Term.app f a) (inferApp aInf fInf a) :=
  match fInf with
  | none => InferHas.noneIntro
  | some fTy =>
      match fTy with
      | Term.var _ => InferHas.noneIntro
      | Term.app _ _ => InferHas.noneIntro
      | Term.lam _ _ => InferHas.noneIntro
      | Term.pi _ _ =>
          match aInf with
          | none => InferHas.noneIntro
          | some _ => by
              unfold inferApp
              unfold inferAppArg
              exact InferHas.app_if (InferHas.some_has hf rfl) (InferHas.some_has ha rfl)
      | Term.sort => InferHas.noneIntro

theorem InferHas.lam {Γ : Ctx} {dom body : Term}
    (domInf bodyInf : Option Term)
    (hdom : InferHas Γ dom domInf)
    (hbody : InferHas (dom :: Γ) body bodyInf) :
    InferHas Γ (Term.lam dom body) (inferLam bodyInf domInf dom) :=
  match domInf with
  | none => InferHas.noneIntro
  | some domTy =>
      match domTy with
      | Term.var _ => InferHas.noneIntro
      | Term.app _ _ => InferHas.noneIntro
      | Term.lam _ _ => InferHas.noneIntro
      | Term.pi _ _ => InferHas.noneIntro
      | Term.sort =>
          match bodyInf with
          | none => InferHas.noneIntro
          | some bodyTy =>
              InferHas.someIntro (Term.pi dom bodyTy)
                (HasType.lamRule Γ dom body bodyTy
                  (InferHas.some_has hdom rfl)
                  (InferHas.some_has hbody rfl))

theorem InferHas.pi {Γ : Ctx} {dom cod : Term}
    (domInf codInf : Option Term)
    (hdom : InferHas Γ dom domInf)
    (hcod : InferHas (dom :: Γ) cod codInf) :
    InferHas Γ (Term.pi dom cod) (inferPi codInf domInf) :=
  match domInf with
  | none => InferHas.noneIntro
  | some domTy =>
      match domTy with
      | Term.var _ => InferHas.noneIntro
      | Term.app _ _ => InferHas.noneIntro
      | Term.lam _ _ => InferHas.noneIntro
      | Term.pi _ _ => InferHas.noneIntro
      | Term.sort =>
          match codInf with
          | none => InferHas.noneIntro
          | some codTy =>
              match codTy with
              | Term.var _ => InferHas.noneIntro
              | Term.app _ _ => InferHas.noneIntro
              | Term.lam _ _ => InferHas.noneIntro
              | Term.pi _ _ => InferHas.noneIntro
              | Term.sort =>
                  InferHas.someIntro Term.sort
                    (HasType.piRule Γ dom cod
                      (InferHas.some_has hdom rfl)
                      (InferHas.some_has hcod rfl))

theorem infer_has (Γ : Ctx) : (t : Term) → InferHas Γ t (infer Γ t)
  | Term.var i => by
      unfold infer
      exact
        match h : Γ.lookup i with
        | none => InferHas.noneIntro
        | some A => InferHas.someIntro A (HasType.varRule Γ i A h)
  | Term.app f a => by
      unfold infer
      exact InferHas.app (infer Γ f) (infer Γ a) (infer_has Γ f) (infer_has Γ a)
  | Term.lam dom body => by
      unfold infer
      exact InferHas.lam (infer Γ dom) (infer (dom :: Γ) body)
        (infer_has Γ dom) (infer_has (dom :: Γ) body)
  | Term.pi dom cod => by
      unfold infer
      exact InferHas.pi (infer Γ dom) (infer (dom :: Γ) cod)
        (infer_has Γ dom) (infer_has (dom :: Γ) cod)
  | Term.sort => by
      unfold infer
      exact InferHas.someIntro Term.sort (HasType.sortRule Γ)

theorem infer_sound
    {Γ : Ctx} {t A : Term}
    (h : infer Γ t = some A) :
    HasType Γ t A :=
  InferHas.some_has (infer_has Γ t) h

/-- Decidable check: 给定 Γ t A, 检查 t 在 Γ 下是否类型为 A。 -/
def check (Γ : Ctx) (t A : Term) : Bool :=
  match infer Γ t with
  | some inferred => Term.beq inferred A
  | none => false

theorem check_sound_some {Γ : Ctx} {t inferred A : Term}
    (ht : HasType Γ t inferred)
    (h : Term.beq inferred A = true) :
    HasType Γ t A :=
  match Term.beq_eq h with
  | rfl => ht

theorem check_sound_aux {Γ : Ctx} {t A : Term}
    (inf : Option Term)
    (h :
      (match inf with
      | some inferred => Term.beq inferred A
      | none => false) = true)
    (hinf : InferHas Γ t inf) :
    HasType Γ t A :=
  match inf with
  | none => nomatch h
  | some _ =>
      check_sound_some (InferHas.some_has hinf rfl) h

theorem check_sound {Γ : Ctx} {t A : Term} (h : check Γ t A = true) :
    HasType Γ t A := by
  unfold check at h
  exact check_sound_aux (infer Γ t) h (infer_has Γ t)

example : check [] Term.sort Term.sort = true := rfl

example : check [Term.sort] (Term.var 0) Term.sort = true := rfl

end BEDC.MetaCIC
