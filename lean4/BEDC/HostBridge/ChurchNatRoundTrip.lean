import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchNatRec
import BEDC.HostBridge.MetaCICTransport
import BEDC.HostBridge.EquationalLaws

namespace BEDC.HostBridge

open BEDC.MetaCIC

abbrev church_zero : Term :=
  churchZeroTm

abbrev church_succ : Term :=
  churchSuccTm

def termEq : Term → Term → Bool
  | Term.var i, t =>
      match t with
      | Term.var j => Nat.beq i j
      | Term.app _ _ => false
      | Term.lam _ _ => false
      | Term.pi _ _ => false
      | Term.sort => false
  | Term.app f a, t =>
      match t with
      | Term.app g b =>
          match termEq f g with
          | true => termEq a b
          | false => false
      | Term.var _ => false
      | Term.lam _ _ => false
      | Term.pi _ _ => false
      | Term.sort => false
  | Term.lam d b, t =>
      match t with
      | Term.lam e c =>
          match termEq d e with
          | true => termEq b c
          | false => false
      | Term.var _ => false
      | Term.app _ _ => false
      | Term.pi _ _ => false
      | Term.sort => false
  | Term.pi d c, t =>
      match t with
      | Term.pi e k =>
          match termEq d e with
          | true => termEq c k
          | false => false
      | Term.var _ => false
      | Term.app _ _ => false
      | Term.lam _ _ => false
      | Term.sort => false
  | Term.sort, t =>
      match t with
      | Term.sort => true
      | Term.var _ => false
      | Term.app _ _ => false
      | Term.lam _ _ => false
      | Term.pi _ _ => false

def hostNatToChurch : Nat → Term
  | 0 => church_zero
  | n + 1 => Term.app church_succ (hostNatToChurch n)

def churchIterBodyToHostNat : Term → Nat → Nat
  | t, fuel =>
      match fuel with
      | 0 => 0
      | fuel + 1 =>
          match t with
          | Term.var _ => 0
          | Term.app f rest =>
              match termEq f (Term.var 1) with
              | true => churchIterBodyToHostNat rest fuel + 1
              | false => 0
          | Term.lam _ _ => 0
          | Term.pi _ _ => 0
          | Term.sort => 0

def churchNormalToHostNat : Term → Nat → Nat
  | t, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        match t with
        | Term.lam d outer =>
            match termEq d Term.sort with
            | true =>
                match outer with
                | Term.lam d2 inner =>
                    match termEq d2 (Term.pi (Term.var 0) (Term.var 1)) with
                    | true =>
                        match inner with
                        | Term.lam d3 body =>
                            match termEq d3 (Term.var 1) with
                            | true => churchIterBodyToHostNat body fuel
                            | false => 0
                        | Term.var _ => 0
                        | Term.app _ _ => 0
                        | Term.pi _ _ => 0
                        | Term.sort => 0
                    | false => 0
                | Term.var _ => 0
                | Term.app _ _ => 0
                | Term.pi _ _ => 0
                | Term.sort => 0
            | false => 0
        | Term.var _ => 0
        | Term.app _ _ => 0
        | Term.pi _ _ => 0
        | Term.sort => 0

def churchSuccSpineToHostNat : Term → Nat → Nat
  | t, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        match termEq t church_zero with
        | true => 0
        | false =>
            match t with
            | Term.app f n =>
                match termEq f church_succ with
                | true => churchSuccSpineToHostNat n fuel + 1
                | false => churchNormalToHostNat (normalizeBounded fuel t) fuel
            | Term.var _ => churchNormalToHostNat (normalizeBounded fuel t) fuel
            | Term.lam _ _ => churchNormalToHostNat (normalizeBounded fuel t) fuel
            | Term.pi _ _ => churchNormalToHostNat (normalizeBounded fuel t) fuel
            | Term.sort => churchNormalToHostNat (normalizeBounded fuel t) fuel

def churchToHostNat (t : Term) (fuel : Nat) : Nat :=
  churchSuccSpineToHostNat t fuel

theorem hostNatToChurch_typed (n : Nat) :
    HasType [] (hostNatToChurch n) churchNatTy := by
  induction n with
  | zero =>
      exact BEDC.MetaCIC.church_zero
  | succ n ih =>
      exact HasType.appRule
        []
        church_succ
        (hostNatToChurch n)
        churchNatTy
        churchNatTy
        BEDC.MetaCIC.church_succ
        ih

theorem hostNatToChurch_closed (n : Nat) :
    ClosedAt 0 (hostNatToChurch n) := by
  induction n with
  | zero =>
      exact BEDC.MetaCIC.ChurchNatRec.church_zero_closed
  | succ n ih =>
      apply ClosedAt.appClosed
      · exact BEDC.MetaCIC.ChurchNatRec.church_succ_closed
      · exact ih

theorem churchIterBodyToHostNat_var_zero (fuel : Nat) :
    churchIterBodyToHostNat (Term.var 0) fuel = 0 := by
  cases fuel with
  | zero => rfl
  | succ fuel => rfl

theorem churchIterBodyToHostNat_step (body : Term) (fuel : Nat) :
    churchIterBodyToHostNat (Term.app (Term.var 1) body) (fuel + 1) =
      churchIterBodyToHostNat body fuel + 1 := by
  rfl

abbrev churchIterBody : Nat → Term
  | 0 => Term.var 0
  | n + 1 => Term.app (Term.var 1) (churchIterBody n)

abbrev churchNormalNat : Nat → Term
  | n =>
      Term.lam Term.sort
        (Term.lam (Term.pi (Term.var 0) (Term.var 1))
          (Term.lam (Term.var 1) (churchIterBody n)))

theorem churchNormalToHostNat_body
    (n fuel : Nat) :
    churchIterBodyToHostNat (churchIterBody n) (fuel + n) = n := by
  induction n generalizing fuel with
  | zero =>
      exact churchIterBodyToHostNat_var_zero fuel
  | succ n ih =>
      change
        churchIterBodyToHostNat
          (Term.app (Term.var 1) (churchIterBody n))
          (fuel + (n + 1)) =
          n + 1
      rw [Nat.add_succ]
      change
        churchIterBodyToHostNat
          (Term.app (Term.var 1) (churchIterBody n))
          ((fuel + n) + 1) =
          n + 1
      rw [churchIterBodyToHostNat_step]
      rw [ih fuel]

theorem churchNormalToHostNat_identity
    (n fuel : Nat) :
    churchNormalToHostNat (churchNormalNat n) ((fuel + n) + 1) = n := by
  change churchIterBodyToHostNat (churchIterBody n) (fuel + n) = n
  exact churchNormalToHostNat_body n fuel

theorem churchSuccSpineToHostNat_identity (n fuel : Nat) :
    churchSuccSpineToHostNat (hostNatToChurch n) (fuel + n) = n := by
  induction n generalizing fuel with
  | zero =>
      cases fuel with
      | zero => rfl
      | succ fuel => rfl
  | succ n ih =>
      change
        churchSuccSpineToHostNat
          (Term.app church_succ (hostNatToChurch n))
          (fuel + (n + 1)) =
          n + 1
      rw [Nat.add_succ]
      change
        churchSuccSpineToHostNat
          (Term.app church_succ (hostNatToChurch n))
          ((fuel + n) + 1) =
          n + 1
      change
        churchSuccSpineToHostNat (hostNatToChurch n) (fuel + n) + 1 =
          n + 1
      rw [ih fuel]

theorem roundtrip_fuel_shape (n : Nat) :
    1000 + n * 10 = (1000 + n * 9) + n := by
  rw [show n * 10 = n * 9 + n by rfl]
  rw [Nat.add_assoc]

theorem hostNat_roundtrip_identity (n : Nat) :
    churchToHostNat (hostNatToChurch n) (1000 + n * 10) = n := by
  unfold churchToHostNat
  rw [roundtrip_fuel_shape n]
  exact churchSuccSpineToHostNat_identity n (1000 + n * 9)

example : hostNatToChurch 0 = church_zero := rfl

example : hostNatToChurch 1 = Term.app church_succ church_zero := rfl

example :
    hostNatToChurch 2 =
      Term.app church_succ (Term.app church_succ church_zero) := rfl

example : churchToHostNat (hostNatToChurch 0) (1000 + 0 * 10) = 0 := by
  exact hostNat_roundtrip_identity 0

example : churchToHostNat (hostNatToChurch 1) (1000 + 1 * 10) = 1 := by
  exact hostNat_roundtrip_identity 1

example : churchToHostNat (hostNatToChurch 2) (1000 + 2 * 10) = 2 := by
  exact hostNat_roundtrip_identity 2

example : churchToHostNat (hostNatToChurch 3) (1000 + 3 * 10) = 3 := by
  exact hostNat_roundtrip_identity 3

end BEDC.HostBridge
