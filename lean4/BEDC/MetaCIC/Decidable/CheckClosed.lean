import BEDC.MetaCIC.Decidable.CheckClosedAtom
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

def isSortType : Term → Option Unit
  | Term.sort => some ()
  | Term.var _ => none
  | Term.app _ _ => none
  | Term.lam _ _ => none
  | Term.pi _ _ => none

def isPiType : Term → Option (Term × Term)
  | Term.sort => none
  | Term.var _ => none
  | Term.app _ _ => none
  | Term.lam _ _ => none
  | Term.pi d c => some (d, c)

def sameTypeResult (A dom cod a : Term) : Option Term :=
  match Term.eq A dom with
  | true => some (substitute 0 a cod)
  | false => none

def inferTypeCtx : Ctx → Term → Option Term
  | _, Term.sort => some Term.sort
  | Γ, Term.var i => Γ.lookup i
  | Γ, Term.pi dom cod =>
      match inferTypeCtx Γ dom with
      | some domTy =>
          match isSortType domTy with
          | some () =>
              match inferTypeCtx ((shift 0 1 dom) :: Γ) cod with
              | some codTy =>
                  match isSortType codTy with
                  | some () => some Term.sort
                  | none => none
              | none => none
          | none => none
      | none => none
  | Γ, Term.lam dom body =>
      match inferTypeCtx Γ dom with
      | some domTy =>
          match isSortType domTy with
          | some () =>
              match inferTypeCtx ((shift 0 1 dom) :: Γ) body with
              | some bodyType => some (Term.pi dom bodyType)
              | none => none
          | none => none
      | none => none
  | Γ, Term.app f a =>
      match inferTypeCtx Γ f with
      | some fTy =>
          match isPiType fTy with
          | some piParts =>
              match inferTypeCtx Γ a with
              | some A => sameTypeResult A piParts.fst piParts.snd a
              | none => none
          | none => none
      | none => none

def inferTypeCtxClosed : Term → Option Term :=
  inferTypeCtx []

theorem isSortType_some_implies_sort {t : Term} :
    isSortType t = some () → t = Term.sort := by
  cases t with
  | sort =>
      intro _
      rfl
  | var i =>
      intro h
      cases h
  | app f a =>
      intro h
      cases h
  | lam dom body =>
      intro h
      cases h
  | pi dom cod =>
      intro h
      cases h

theorem isSortType_sort :
    isSortType Term.sort = some () :=
  rfl

theorem isSortType_none_of_not_sort {t : Term} :
    (t = Term.sort → False) → isSortType t = none := by
  intro hne
  cases t with
  | sort =>
      exact False.elim (hne rfl)
  | var i =>
      rfl
  | app f a =>
      rfl
  | lam dom body =>
      rfl
  | pi dom cod =>
      rfl

theorem isPiType_some_implies_pi {t d c : Term} :
    isPiType t = some (d, c) → t = Term.pi d c := by
  cases t with
  | sort =>
      intro h
      cases h
  | var i =>
      intro h
      cases h
  | app f a =>
      intro h
      cases h
  | lam dom body =>
      intro h
      cases h
  | pi dom cod =>
      intro h
      cases h
      rfl

theorem isPiType_pi (d c : Term) :
    isPiType (Term.pi d c) = some (d, c) :=
  rfl

theorem isPiType_none_of_not_pi {t : Term} :
    ((d c : Term) → t = Term.pi d c → False) → isPiType t = none := by
  intro hne
  cases t with
  | sort =>
      rfl
  | var i =>
      rfl
  | app f a =>
      rfl
  | lam dom body =>
      rfl
  | pi dom cod =>
      exact False.elim (hne dom cod rfl)

theorem sameTypeResult_eq_checkSameTerm (A dom cod a : Term) :
    sameTypeResult A dom cod a =
      match checkSameTerm A dom with
      | some () => some (substitute 0 a cod)
      | none => none := by
  unfold sameTypeResult
  unfold checkSameTerm
  cases Term.eq A dom with
  | false =>
      rfl
  | true =>
      rfl

theorem inferTypeCtx_eq_inferType (Γ : Ctx) (t : Term) :
    inferTypeCtx Γ t = inferType Γ t := by
  induction t generalizing Γ with
  | sort =>
      rfl
  | var i =>
      rfl
  | pi dom cod ihdom ihcod =>
      unfold inferTypeCtx
      unfold inferType
      rw [ihdom Γ]
      cases hdom : inferType Γ dom with
      | none =>
          rfl
      | some domTy =>
          cases domTy with
          | sort =>
              change
                (match inferTypeCtx ((shift 0 1 dom) :: Γ) cod with
                | some codTy =>
                    match isSortType codTy with
                    | some () => some Term.sort
                    | none => none
                | none => none) =
                match inferType ((shift 0 1 dom) :: Γ) cod with
                | some Term.sort => some Term.sort
                | some (Term.var _) => none
                | some (Term.app _ _) => none
                | some (Term.lam _ _) => none
                | some (Term.pi _ _) => none
                | none => none
              rw [ihcod ((shift 0 1 dom) :: Γ)]
              cases hcod : inferType ((shift 0 1 dom) :: Γ) cod with
              | none =>
                  rfl
              | some codTy =>
                  cases codTy with
                  | sort =>
                      rfl
                  | var i =>
                      rfl
                  | app f a =>
                      rfl
                  | lam d b =>
                      rfl
                  | pi d c =>
                      rfl
          | var i =>
              rfl
          | app f a =>
              rfl
          | lam d b =>
              rfl
          | pi d c =>
              rfl
  | lam dom body ihdom ihbody =>
      unfold inferTypeCtx
      unfold inferType
      rw [ihdom Γ]
      cases hdom : inferType Γ dom with
      | none =>
          rfl
      | some domTy =>
          cases domTy with
          | sort =>
              change
                (match inferTypeCtx ((shift 0 1 dom) :: Γ) body with
                | some bodyType => some (Term.pi dom bodyType)
                | none => none) =
                match inferType ((shift 0 1 dom) :: Γ) body with
              | some cod => some (Term.pi dom cod)
              | none => none
              rw [ihbody ((shift 0 1 dom) :: Γ)]
          | var i =>
              rfl
          | app f a =>
              rfl
          | lam d b =>
              rfl
          | pi d c =>
              rfl
  | app f a ihf iha =>
      unfold inferTypeCtx
      unfold inferType
      rw [ihf Γ]
      cases hf : inferType Γ f with
      | none =>
          rfl
      | some fTy =>
          cases fTy with
          | pi dom cod =>
              change
                (match inferTypeCtx Γ a with
                | some A => sameTypeResult A dom cod a
                | none => none) =
                match inferType Γ a with
                | some A =>
                    match checkSameTerm A dom with
                    | some () => some (substitute 0 a cod)
                    | none => none
                | none => none
              rw [iha Γ]
              cases ha : inferType Γ a with
              | none =>
                  rfl
              | some A =>
                  exact sameTypeResult_eq_checkSameTerm A dom cod a
          | sort =>
              rfl
          | var i =>
              rfl
          | app g b =>
              rfl
          | lam d b =>
              rfl

theorem inferTypeCtx_sound (Γ : Ctx) (t A : Term)
    (h : inferTypeCtx Γ t = some A) :
    HasType Γ t A := by
  rw [inferTypeCtx_eq_inferType Γ t] at h
  exact inferType_sound Γ t A h

theorem inferTypeCtx_complete (Γ : Ctx) (t A : Term)
    (h : HasType Γ t A) :
    inferTypeCtx Γ t = some A := by
  rw [inferTypeCtx_eq_inferType Γ t]
  exact inferType_complete Γ t A h

theorem inferTypeCtx_complete_sort (Γ : Ctx) :
    inferTypeCtx Γ Term.sort = some Term.sort :=
  rfl

theorem inferTypeCtx_complete_var {Γ : Ctx} {i : Idx} {A : Term}
    (hlookup : Γ.lookup i = some A) :
    inferTypeCtx Γ (Term.var i) = some A :=
  hlookup

theorem inferTypeCtx_complete_pi (Γ : Ctx) (dom cod : Term)
    (hT : HasType Γ (Term.pi dom cod) Term.sort) :
    inferTypeCtx Γ (Term.pi dom cod) = some Term.sort :=
  inferTypeCtx_complete Γ (Term.pi dom cod) Term.sort hT

theorem inferTypeCtx_complete_lam {Γ : Ctx} {dom body cod : Term}
    (hT : HasType Γ (Term.lam dom body) (Term.pi dom cod)) :
    inferTypeCtx Γ (Term.lam dom body) = some (Term.pi dom cod) :=
  inferTypeCtx_complete Γ (Term.lam dom body) (Term.pi dom cod) hT

theorem inferTypeCtx_complete_app {Γ : Ctx} {f a dom cod : Term}
    (_hT : HasType Γ (Term.app f a) (substitute 0 a cod))
    (hf : HasType Γ f (Term.pi dom cod))
    (ha : HasType Γ a dom) :
    inferTypeCtx Γ (Term.app f a) = some (substitute 0 a cod) := by
  exact inferTypeCtx_complete Γ (Term.app f a) (substitute 0 a cod)
    (HasType.appRule Γ f a dom cod hf ha)

theorem inferTypeCtxClosed_sound (t A : Term)
    (h : inferTypeCtxClosed t = some A) (_hclosed : ClosedAt 0 t) :
    HasType [] t A :=
  inferTypeCtx_sound [] t A h

theorem inferTypeCtxClosed_complete (t A : Term)
    (h : HasType [] t A) :
    inferTypeCtxClosed t = some A :=
  inferTypeCtx_complete [] t A h

theorem inferTypeCtx_dependent_identity_nonempty :
    inferTypeCtx [Term.sort]
      (Term.lam (Term.var 0) (Term.var 0)) =
      some (Term.pi (Term.var 0) (Term.var 1)) :=
  inferTypeCtx_complete [Term.sort]
    (Term.lam (Term.var 0) (Term.var 0))
    (Term.pi (Term.var 0) (Term.var 1))
    dependent_identity_tracks_outer_domain

theorem inferTypeCtx_pi_dependent_identity_nonempty :
    inferTypeCtx [Term.sort]
      (Term.pi (Term.var 0) (Term.var 1)) =
      some Term.sort :=
  inferTypeCtx_complete [Term.sort]
    (Term.pi (Term.var 0) (Term.var 1))
    Term.sort
    pi_dependent_identity_type

theorem inferTypeCtxClosed_var_empty_none (i : Idx) :
    inferTypeCtxClosed (Term.var i) = none :=
  rfl

end BEDC.MetaCIC
