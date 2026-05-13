import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchAlgebra
import BEDC.HostBridge.MetaCICTransport
import BEDC.HostBridge.EquationalLaws

namespace BEDC.HostBridge

open BEDC.MetaCIC

abbrev church_true : Term :=
  churchTrueTm

abbrev church_false : Term :=
  churchFalseTm

abbrev church_mk_pair : Term :=
  churchMkPairTm

abbrev church_fst : Term :=
  churchFstTm

abbrev church_snd : Term :=
  churchSndTm

abbrev church_bool_ty : Term :=
  churchBoolTy

abbrev church_bool_pair_ty : Term :=
  Term.app (Term.app churchPairFormerTm churchBoolTy) churchBoolTy

def hostBoolToChurch : Bool → Term
  | true => church_true
  | false => church_false

def churchNormalToHostBool : Term → Bool
  | Term.lam d outer =>
      match d with
      | Term.sort =>
          match outer with
          | Term.lam d₂ inner =>
              match d₂ with
              | Term.var 0 =>
                  match inner with
                  | Term.lam d₃ body =>
                      match d₃ with
                      | Term.var 1 =>
                          match body with
                          | Term.var 1 => true
                          | Term.var 0 => false
                          | Term.var (_ + 2) => false
                          | Term.app _ _ => false
                          | Term.lam _ _ => false
                          | Term.pi _ _ => false
                          | Term.sort => false
                      | Term.var 0 => false
                      | Term.var (_ + 2) => false
                      | Term.app _ _ => false
                      | Term.lam _ _ => false
                      | Term.pi _ _ => false
                      | Term.sort => false
                  | Term.var _ => false
                  | Term.app _ _ => false
                  | Term.pi _ _ => false
                  | Term.sort => false
              | Term.var (_ + 1) => false
              | Term.app _ _ => false
              | Term.lam _ _ => false
              | Term.pi _ _ => false
              | Term.sort => false
          | Term.var _ => false
          | Term.app _ _ => false
          | Term.pi _ _ => false
          | Term.sort => false
      | Term.var _ => false
      | Term.app _ _ => false
      | Term.lam _ _ => false
      | Term.pi _ _ => false
  | Term.var _ => false
  | Term.app _ _ => false
  | Term.pi _ _ => false
  | Term.sort => false

def churchToHostBool (t : Term) (fuel : Nat) : Bool :=
  churchNormalToHostBool (normalizeBounded fuel t)

def hostBoolPairToChurch : Bool × Bool → Term
  | (a, b) =>
      churchPairValue churchBoolTy churchBoolTy
        (hostBoolToChurch a)
        (hostBoolToChurch b)

abbrev churchBoolPairFst (p : Term) : Term :=
  Term.app (Term.app (Term.app church_fst churchBoolTy) churchBoolTy) p

abbrev churchBoolPairSnd (p : Term) : Term :=
  Term.app (Term.app (Term.app church_snd churchBoolTy) churchBoolTy) p

def churchPairToHostBoolPair (t : Term) (fuel : Nat) : Bool × Bool :=
  (churchToHostBool (churchBoolPairFst t) fuel,
    churchToHostBool (churchBoolPairSnd t) fuel)

theorem hostBoolToChurch_typed (b : Bool) :
    HasType [] (hostBoolToChurch b) churchBoolTy := by
  cases b with
  | false =>
      exact BEDC.MetaCIC.church_false
  | true =>
      exact BEDC.MetaCIC.church_true

theorem church_bool_ty_closed :
    ClosedAt 0 churchBoolTy := by
  unfold churchBoolTy
  apply ClosedAt.piClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.piClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.piClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 2

theorem church_true_closed :
    ClosedAt 0 church_true := by
  unfold church_true churchTrueTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact (show 1 < 3 from Nat.succ_lt_succ (Nat.zero_lt_succ 1))

theorem church_false_closed :
    ClosedAt 0 church_false := by
  unfold church_false churchFalseTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.varClosed
        exact (show 0 < 3 from Nat.zero_lt_succ 2)

theorem hostBoolToChurch_closed (b : Bool) :
    ClosedAt 0 (hostBoolToChurch b) := by
  cases b with
  | false =>
      exact church_false_closed
  | true =>
      exact church_true_closed

theorem churchNormalToHostBool_true :
    churchNormalToHostBool church_true = true := by
  rfl

theorem churchNormalToHostBool_false :
    churchNormalToHostBool church_false = false := by
  rfl

theorem normalize_hostBoolToChurch (b : Bool) :
    normalizeBounded 4 (hostBoolToChurch b) = hostBoolToChurch b := by
  cases b with
  | false =>
      rfl
  | true =>
      rfl

theorem hostBool_roundtrip_identity (b : Bool) :
    churchToHostBool (hostBoolToChurch b) 4 = b := by
  unfold churchToHostBool
  rw [normalize_hostBoolToChurch b]
  cases b with
  | false =>
      rfl
  | true =>
      rfl

theorem churchBool_apply_to_host_branches
    (b : Bool) (X x y : Term)
    (hX : ClosedAt 0 X) (hx : ClosedAt 0 x) (hy : ClosedAt 0 y) :
    BetaStarStep
      (Term.app (Term.app (Term.app (hostBoolToChurch b) X) x) y)
      (hostBoolToChurch (if b then true else false) |> fun _ =>
        match b with
        | true => x
        | false => y) := by
  cases b with
  | false =>
      exact BEDC.MetaCIC.church_false_proj X x y hX hx hy
  | true =>
      exact BEDC.MetaCIC.church_true_proj X x y hX hx hy

theorem churchBool_apply_true
    (X x y : Term)
    (hX : ClosedAt 0 X) (hx : ClosedAt 0 x) (hy : ClosedAt 0 y) :
    BetaStarStep
      (Term.app (Term.app (Term.app (hostBoolToChurch true) X) x) y)
      x := by
  exact BEDC.MetaCIC.church_true_proj X x y hX hx hy

theorem churchBool_apply_false
    (X x y : Term)
    (hX : ClosedAt 0 X) (hx : ClosedAt 0 x) (hy : ClosedAt 0 y) :
    BetaStarStep
      (Term.app (Term.app (Term.app (hostBoolToChurch false) X) x) y)
      y := by
  exact BEDC.MetaCIC.church_false_proj X x y hX hx hy

def hostBoolAndChurch (a b : Bool) : Term :=
  Term.app
    (Term.app
      (Term.app (hostBoolToChurch a) churchBoolTy)
      (hostBoolToChurch b))
    church_false

theorem hostBoolAndChurch_closed (a b : Bool) :
    ClosedAt 0 (hostBoolAndChurch a b) := by
  unfold hostBoolAndChurch
  apply ClosedAt.appClosed
  · apply ClosedAt.appClosed
    · apply ClosedAt.appClosed
      · exact hostBoolToChurch_closed a
      · exact church_bool_ty_closed
    · exact hostBoolToChurch_closed b
  · exact church_false_closed

theorem hostBoolAndChurch_beta
    (a b : Bool) :
    BetaStarStep (hostBoolAndChurch a b) (hostBoolToChurch (a && b)) := by
  cases a with
  | false =>
      change
        BetaStarStep
          (Term.app
            (Term.app
              (Term.app church_false churchBoolTy)
              (hostBoolToChurch b))
            church_false)
          church_false
      exact BEDC.MetaCIC.church_false_proj
        churchBoolTy (hostBoolToChurch b) church_false
        church_bool_ty_closed
        (hostBoolToChurch_closed b)
        church_false_closed
  | true =>
      change
        BetaStarStep
          (Term.app
            (Term.app
              (Term.app church_true churchBoolTy)
              (hostBoolToChurch b))
            church_false)
          (hostBoolToChurch b)
      exact BEDC.MetaCIC.church_true_proj
        churchBoolTy (hostBoolToChurch b) church_false
        church_bool_ty_closed
        (hostBoolToChurch_closed b)
        church_false_closed

theorem hostBoolAnd_roundtrip_identity (a b : Bool) :
    churchToHostBool (hostBoolToChurch (a && b)) 4 = (a && b) := by
  exact hostBool_roundtrip_identity (a && b)

theorem church_mk_pair_closed :
    ClosedAt 0 church_mk_pair := by
  unfold church_mk_pair churchMkPairTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.lt_succ_self 1
      · apply ClosedAt.lamClosed
        · apply ClosedAt.varClosed
          exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)
        · apply ClosedAt.lamClosed
          · exact ClosedAt.sortClosed
          · apply ClosedAt.lamClosed
            · apply ClosedAt.piClosed
              · apply ClosedAt.varClosed
                change 4 < 5
                exact Nat.succ_lt_succ
                  (Nat.succ_lt_succ
                    (Nat.succ_lt_succ
                      (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))
              · apply ClosedAt.piClosed
                · apply ClosedAt.varClosed
                  change 4 < 6
                  exact Nat.succ_lt_succ
                    (Nat.succ_lt_succ
                      (Nat.succ_lt_succ
                        (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))
                · apply ClosedAt.varClosed
                  change 2 < 7
                  exact Nat.succ_lt_succ
                    (Nat.succ_lt_succ (Nat.zero_lt_succ 4))
            · apply ClosedAt.appClosed
              · apply ClosedAt.appClosed
                · apply ClosedAt.varClosed
                  exact Nat.zero_lt_succ 5
                · apply ClosedAt.varClosed
                  change 3 < 6
                  exact Nat.succ_lt_succ
                    (Nat.succ_lt_succ
                      (Nat.succ_lt_succ (Nat.zero_lt_succ 2)))
              · apply ClosedAt.varClosed
                change 2 < 6
                exact Nat.succ_lt_succ
                  (Nat.succ_lt_succ (Nat.zero_lt_succ 3))

theorem hostBoolPairToChurch_closed (p : Bool × Bool) :
    ClosedAt 0 (hostBoolPairToChurch p) := by
  cases p with
  | mk a b =>
      unfold hostBoolPairToChurch churchPairValue churchMkPairTm
      apply ClosedAt.appClosed
      · apply ClosedAt.appClosed
        · apply ClosedAt.appClosed
          · apply ClosedAt.appClosed
            · exact church_mk_pair_closed
            · exact church_bool_ty_closed
          · exact church_bool_ty_closed
        · exact hostBoolToChurch_closed a
      · exact hostBoolToChurch_closed b

theorem hostBoolPairToChurch_selector_beta
    (a b R k : Term)
    (ha : ClosedAt 0 a) (hb : ClosedAt 0 b)
    (_hR : ClosedAt 0 R) (_hk : ClosedAt 0 k) :
    BetaStarStep
      (Term.app
        (Term.app
          (churchPairValue churchBoolTy churchBoolTy a b)
          R)
        k)
      (Term.app (Term.app k a) b) := by
  exact BEDC.MetaCIC.church_pair_value_to_selector
    churchBoolTy churchBoolTy a b R k
    church_bool_ty_closed church_bool_ty_closed ha hb

theorem hostBoolPairToChurch_typed (p : Bool × Bool) :
    ∃ T, HasType [] (hostBoolPairToChurch p) T := by
  cases p with
  | mk a b =>
      unfold hostBoolPairToChurch
      apply Exists.intro
      exact HasType.appRule []
        (Term.app
          (Term.app
            (Term.app churchMkPairTm churchBoolTy)
            churchBoolTy)
          (hostBoolToChurch a))
        (hostBoolToChurch b)
        _
        _
        (HasType.appRule []
          (Term.app
            (Term.app churchMkPairTm churchBoolTy)
            churchBoolTy)
          (hostBoolToChurch a)
          _
          _
          (HasType.appRule []
            (Term.app churchMkPairTm churchBoolTy)
            churchBoolTy
            _
            _
            (HasType.appRule []
              churchMkPairTm
              churchBoolTy
              _
              _
              BEDC.MetaCIC.church_mk_pair
              BEDC.MetaCIC.church_bool_type)
            BEDC.MetaCIC.church_bool_type)
          (hostBoolToChurch_typed a))
        (hostBoolToChurch_typed b)

theorem churchBoolPairFst_normalize (a b : Bool) :
    normalizeBounded 8
      (churchBoolPairFst (hostBoolPairToChurch (a, b))) =
      hostBoolToChurch a := by
  cases a <;> cases b <;> rfl

theorem churchBoolPairSnd_normalize (a b : Bool) :
    normalizeBounded 8
      (churchBoolPairSnd (hostBoolPairToChurch (a, b))) =
      hostBoolToChurch b := by
  cases a <;> cases b <;> rfl

theorem hostBoolPair_roundtrip_identity (p : Bool × Bool) :
    churchPairToHostBoolPair (hostBoolPairToChurch p) 8 = p := by
  cases p with
  | mk a b =>
      unfold churchPairToHostBoolPair churchToHostBool
      rw [churchBoolPairFst_normalize a b]
      rw [churchBoolPairSnd_normalize a b]
      cases a <;> cases b <;> rfl

example : hostBoolToChurch true = church_true := rfl

example : hostBoolToChurch false = church_false := rfl

example :
    churchToHostBool (hostBoolToChurch true) 4 = true := by
  exact hostBool_roundtrip_identity true

example :
    churchToHostBool (hostBoolToChurch false) 4 = false := by
  exact hostBool_roundtrip_identity false

example :
    churchPairToHostBoolPair (hostBoolPairToChurch (true, false)) 8 =
      (true, false) := by
  exact hostBoolPair_roundtrip_identity (true, false)

end BEDC.HostBridge
