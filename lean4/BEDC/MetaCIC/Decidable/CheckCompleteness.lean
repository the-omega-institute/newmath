import BEDC.MetaCIC.Decidable.CheckClosed
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

namespace CheckCompleteness

theorem inferTypeCtx_complete_raw
    (ctx : Ctx) (t A : Term)
    (hT : HasType ctx t A) :
    inferTypeCtx ctx t = some A := by
  induction hT with
  | sortRule Γ =>
      rfl
  | varRule Γ i A hlookup =>
      exact hlookup
  | piRule Γ dom cod hdom hcod ihdom ihcod =>
      unfold inferTypeCtx
      rw [ihdom]
      change
        (match isSortType Term.sort with
        | some () =>
            match inferTypeCtx ((shift 0 1 dom) :: Γ) cod with
            | some codTy =>
                match isSortType codTy with
                | some () => some Term.sort
                | none => none
            | none => none
        | none => none) = some Term.sort
      rw [isSortType_sort]
      rw [ihcod]
      rfl
  | lamRule Γ dom body cod hdom hbody ihdom ihbody =>
      unfold inferTypeCtx
      rw [ihdom]
      change
        (match isSortType Term.sort with
        | some () =>
            match inferTypeCtx ((shift 0 1 dom) :: Γ) body with
            | some bodyType => some (Term.pi dom bodyType)
            | none => none
        | none => none) = some (Term.pi dom cod)
      rw [isSortType_sort]
      rw [ihbody]
  | appRule Γ f a dom cod hf ha ihf iha =>
      unfold inferTypeCtx
      rw [ihf]
      change
        (match isPiType (Term.pi dom cod) with
        | some piParts =>
            match inferTypeCtx Γ a with
            | some A => sameTypeResult A piParts.fst piParts.snd a
            | none => none
        | none => none) = some (substitute 0 a cod)
      rw [isPiType_pi dom cod]
      rw [iha]
      unfold sameTypeResult
      change
        (match Term.eq dom dom with
        | true => some (substitute 0 a cod)
        | false => none) = some (substitute 0 a cod)
      rw [Term.eq_refl dom]

theorem inferTypeCtx_complete_total
    (ctx : Ctx) (t A : Term)
    (hT : HasType ctx t A) :
    ∃ A', inferTypeCtx ctx t = some A' ∧ A' = A := by
  exists A
  constructor
  · exact inferTypeCtx_complete_raw ctx t A hT
  · rfl

theorem inferTypeCtx_complete_sort (ctx : Ctx) :
    inferTypeCtx ctx Term.sort = some Term.sort := by
  rfl

theorem inferTypeCtx_complete_var {ctx : Ctx} {i : Idx} {A : Term}
    (h : ctx.lookup i = some A) :
    inferTypeCtx ctx (Term.var i) = some A := by
  exact h

theorem inferTypeCtx_complete_pi_direct
    (ctx : Ctx) (dom cod : Term)
    (hdom : HasType ctx dom Term.sort)
    (hcod : HasType ((shift 0 1 dom) :: ctx) cod Term.sort) :
    inferTypeCtx ctx (Term.pi dom cod) = some Term.sort := by
  unfold inferTypeCtx
  rw [inferTypeCtx_complete_raw ctx dom Term.sort hdom]
  change
    (match isSortType Term.sort with
    | some () =>
        match inferTypeCtx ((shift 0 1 dom) :: ctx) cod with
        | some codTy =>
            match isSortType codTy with
            | some () => some Term.sort
            | none => none
        | none => none
    | none => none) = some Term.sort
  rw [isSortType_sort]
  rw [inferTypeCtx_complete_raw ((shift 0 1 dom) :: ctx) cod Term.sort hcod]
  rfl

theorem inferTypeCtx_complete_pi
    (ctx : Ctx) (dom cod : Term)
    (hT : HasType ctx (Term.pi dom cod) Term.sort) :
    inferTypeCtx ctx (Term.pi dom cod) = some Term.sort := by
  exact inferTypeCtx_complete_raw ctx (Term.pi dom cod) Term.sort hT

theorem inferTypeCtx_complete_lam_direct
    (ctx : Ctx) (dom body bodyType : Term)
    (hdom : HasType ctx dom Term.sort)
    (hbody : HasType ((shift 0 1 dom) :: ctx) body bodyType) :
    inferTypeCtx ctx (Term.lam dom body) =
      some (Term.pi dom bodyType) := by
  unfold inferTypeCtx
  rw [inferTypeCtx_complete_raw ctx dom Term.sort hdom]
  change
    (match isSortType Term.sort with
    | some () =>
        match inferTypeCtx ((shift 0 1 dom) :: ctx) body with
        | some inferredBodyType => some (Term.pi dom inferredBodyType)
        | none => none
    | none => none) = some (Term.pi dom bodyType)
  rw [isSortType_sort]
  rw [inferTypeCtx_complete_raw
    ((shift 0 1 dom) :: ctx) body bodyType hbody]

theorem inferTypeCtx_complete_lam
    (ctx : Ctx) (dom body bodyType : Term)
    (hT : HasType ctx (Term.lam dom body) (Term.pi dom bodyType)) :
    inferTypeCtx ctx (Term.lam dom body) = some (Term.pi dom bodyType) := by
  exact inferTypeCtx_complete_raw ctx
    (Term.lam dom body) (Term.pi dom bodyType) hT

theorem inferTypeCtx_complete_app_direct
    (ctx : Ctx) (f a dom cod : Term)
    (hf : HasType ctx f (Term.pi dom cod))
    (ha : HasType ctx a dom) :
    inferTypeCtx ctx (Term.app f a) = some (substitute 0 a cod) := by
  unfold inferTypeCtx
  rw [inferTypeCtx_complete_raw ctx f (Term.pi dom cod) hf]
  change
    (match isPiType (Term.pi dom cod) with
    | some piParts =>
        match inferTypeCtx ctx a with
        | some A => sameTypeResult A piParts.fst piParts.snd a
        | none => none
    | none => none) = some (substitute 0 a cod)
  rw [isPiType_pi dom cod]
  rw [inferTypeCtx_complete_raw ctx a dom ha]
  unfold sameTypeResult
  change
    (match Term.eq dom dom with
    | true => some (substitute 0 a cod)
    | false => none) = some (substitute 0 a cod)
  rw [Term.eq_refl dom]

theorem inferTypeCtx_complete_app
    (ctx : Ctx) (f a dom cod : Term)
    (hf : HasType ctx f (Term.pi dom cod))
    (ha : HasType ctx a dom) :
    inferTypeCtx ctx (Term.app f a) = some (substitute 0 a cod) := by
  exact inferTypeCtx_complete_app_direct ctx f a dom cod hf ha

theorem inferTypeCtx_complete_sort_exists (ctx : Ctx) :
    ∃ A', inferTypeCtx ctx Term.sort = some A' ∧ A' = Term.sort := by
  exact inferTypeCtx_complete_total ctx Term.sort Term.sort
    (HasType.sortRule ctx)

theorem inferTypeCtx_complete_var_exists
    {ctx : Ctx} {i : Idx} {A : Term}
    (h : ctx.lookup i = some A) :
    ∃ A', inferTypeCtx ctx (Term.var i) = some A' ∧ A' = A := by
  exact inferTypeCtx_complete_total ctx (Term.var i) A
    (HasType.varRule ctx i A h)

theorem inferTypeCtx_complete_pi_exists
    (ctx : Ctx) (dom cod : Term)
    (hT : HasType ctx (Term.pi dom cod) Term.sort) :
    ∃ A', inferTypeCtx ctx (Term.pi dom cod) = some A' ∧ A' = Term.sort := by
  exists Term.sort
  constructor
  · exact inferTypeCtx_complete_pi ctx dom cod hT
  · rfl

theorem inferTypeCtx_complete_lam_exists
    (ctx : Ctx) (dom body bodyType : Term)
    (hT : HasType ctx (Term.lam dom body) (Term.pi dom bodyType)) :
    ∃ A',
      inferTypeCtx ctx (Term.lam dom body) = some A'
        ∧ A' = Term.pi dom bodyType := by
  exists Term.pi dom bodyType
  constructor
  · exact inferTypeCtx_complete_lam ctx dom body bodyType hT
  · rfl

theorem inferTypeCtx_complete_app_exists
    (ctx : Ctx) (f a dom cod : Term)
    (hf : HasType ctx f (Term.pi dom cod))
    (ha : HasType ctx a dom) :
    ∃ A',
      inferTypeCtx ctx (Term.app f a) = some A'
        ∧ A' = substitute 0 a cod := by
  exists substitute 0 a cod
  constructor
  · exact inferTypeCtx_complete_app ctx f a dom cod hf ha
  · rfl

theorem inferTypeCtx_complete_via_shape
    (ctx : Ctx) (t A : Term)
    (hT : HasType ctx t A) :
    ∃ A', inferTypeCtx ctx t = some A' ∧ A' = A := by
  exact inferTypeCtx_complete_total ctx t A hT

end CheckCompleteness

theorem inferTypeCtx_complete_strict
    (ctx : Ctx) (t A : Term)
    (hT : HasType ctx t A) :
    ∃ A', inferTypeCtx ctx t = some A' ∧ A' = A :=
  CheckCompleteness.inferTypeCtx_complete_total ctx t A hT

end BEDC.MetaCIC
