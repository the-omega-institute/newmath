namespace BEDC.Foundations.TriangleGenerationSystem

/-!
`TriAxisObjCode` is a generated syntax universe.  The projection below is a
recursive function of code shape, not a stored certificate field.  The
architecture slogan that every mathematical object is triangular is intentionally
not stated as a theorem here; this file proves the generated-code metatheorem.
-/

structure TriAxisProfile where
  distinction : Nat
  time : Nat
  symmetry : Nat
deriving Repr, DecidableEq

def TriAxisProfile.zero : TriAxisProfile :=
  { distinction := 0, time := 0, symmetry := 0 }

def TriAxisProfile.distinctionStep (p : TriAxisProfile) : TriAxisProfile :=
  { p with distinction := p.distinction + 1 }

def TriAxisProfile.timeStep (p : TriAxisProfile) : TriAxisProfile :=
  { p with time := p.time + 1 }

def TriAxisProfile.symmetryStep (p : TriAxisProfile) : TriAxisProfile :=
  { p with symmetry := p.symmetry + 1 }

def TriAxisProfile.merge (p q : TriAxisProfile) : TriAxisProfile :=
  { distinction := p.distinction + q.distinction,
    time := p.time + q.time,
    symmetry := p.symmetry + q.symmetry }

inductive TriAxisObjCode : Type where
  | base : TriAxisObjCode
  | distinctionGen : TriAxisObjCode → TriAxisObjCode
  | timeGen : TriAxisObjCode → TriAxisObjCode
  | symmetryGen : TriAxisObjCode → TriAxisObjCode
  | pairGen : TriAxisObjCode → TriAxisObjCode → TriAxisObjCode
deriving Repr, DecidableEq

def triAxisProjection : TriAxisObjCode → TriAxisProfile
  | TriAxisObjCode.base => TriAxisProfile.zero
  | TriAxisObjCode.distinctionGen c =>
      TriAxisProfile.distinctionStep (triAxisProjection c)
  | TriAxisObjCode.timeGen c =>
      TriAxisProfile.timeStep (triAxisProjection c)
  | TriAxisObjCode.symmetryGen c =>
      TriAxisProfile.symmetryStep (triAxisProjection c)
  | TriAxisObjCode.pairGen left right =>
      TriAxisProfile.merge (triAxisProjection left) (triAxisProjection right)

inductive IsProjectionOf : TriAxisObjCode → TriAxisProfile → Prop where
  | base : IsProjectionOf TriAxisObjCode.base TriAxisProfile.zero
  | distinctionGen {c : TriAxisObjCode} {p : TriAxisProfile} :
      IsProjectionOf c p →
      IsProjectionOf (TriAxisObjCode.distinctionGen c)
        (TriAxisProfile.distinctionStep p)
  | timeGen {c : TriAxisObjCode} {p : TriAxisProfile} :
      IsProjectionOf c p →
      IsProjectionOf (TriAxisObjCode.timeGen c)
        (TriAxisProfile.timeStep p)
  | symmetryGen {c : TriAxisObjCode} {p : TriAxisProfile} :
      IsProjectionOf c p →
      IsProjectionOf (TriAxisObjCode.symmetryGen c)
        (TriAxisProfile.symmetryStep p)
  | pairGen {left right : TriAxisObjCode} {p q : TriAxisProfile} :
      IsProjectionOf left p →
      IsProjectionOf right q →
      IsProjectionOf (TriAxisObjCode.pairGen left right)
        (TriAxisProfile.merge p q)

theorem triAxisProjection_is_projection :
    ∀ c : TriAxisObjCode, IsProjectionOf c (triAxisProjection c)
  | TriAxisObjCode.base => IsProjectionOf.base
  | TriAxisObjCode.distinctionGen c =>
      IsProjectionOf.distinctionGen (triAxisProjection_is_projection c)
  | TriAxisObjCode.timeGen c =>
      IsProjectionOf.timeGen (triAxisProjection_is_projection c)
  | TriAxisObjCode.symmetryGen c =>
      IsProjectionOf.symmetryGen (triAxisProjection_is_projection c)
  | TriAxisObjCode.pairGen left right =>
      IsProjectionOf.pairGen
        (triAxisProjection_is_projection left)
        (triAxisProjection_is_projection right)

theorem triAxisProjection_relation_forced :
    ∀ {c : TriAxisObjCode} {p : TriAxisProfile},
      IsProjectionOf c p → p = triAxisProjection c
  | _, _, IsProjectionOf.base => rfl
  | _, _, IsProjectionOf.distinctionGen h => by
      cases triAxisProjection_relation_forced h
      rfl
  | _, _, IsProjectionOf.timeGen h => by
      cases triAxisProjection_relation_forced h
      rfl
  | _, _, IsProjectionOf.symmetryGen h => by
      cases triAxisProjection_relation_forced h
      rfl
  | _, _, IsProjectionOf.pairGen hLeft hRight => by
      cases triAxisProjection_relation_forced hLeft
      cases triAxisProjection_relation_forced hRight
      rfl

def ExistsUniqueProjection (c : TriAxisObjCode) : Prop :=
  IsProjectionOf c (triAxisProjection c) ∧
    ∀ p : TriAxisProfile, IsProjectionOf c p → p = triAxisProjection c

def ExistsUniqueProjectionSigma (c : TriAxisObjCode) : Prop :=
  ∃ p : TriAxisProfile, IsProjectionOf c p ∧
    ∀ q : TriAxisProfile, IsProjectionOf c q → q = p

theorem triAxisProjection_forced_unique
    (c : TriAxisObjCode) : ExistsUniqueProjection c :=
  ⟨triAxisProjection_is_projection c, fun _p hp =>
    triAxisProjection_relation_forced hp⟩

theorem triAxisProjection_forced_unique_sigma
    (c : TriAxisObjCode) : ExistsUniqueProjectionSigma c :=
  ⟨triAxisProjection c, triAxisProjection_is_projection c, fun _q hq =>
    triAxisProjection_relation_forced hq⟩

theorem triAxisProjection_forced_unique_pair
    (left right : TriAxisObjCode) :
    triAxisProjection (TriAxisObjCode.pairGen left right) =
      TriAxisProfile.merge (triAxisProjection left) (triAxisProjection right) :=
  rfl

structure VisibleSymmetryShape where
  Carrier : Type
  rel : Carrier → Carrier → Prop
  refl : ∀ a : Carrier, rel a a
  symm : ∀ {a b : Carrier}, rel a b → rel b a
  trans : ∀ {a b c : Carrier}, rel a b → rel b c → rel a c

def natAsObjCode : Nat → TriAxisObjCode
  | 0 => TriAxisObjCode.base
  | n + 1 => TriAxisObjCode.timeGen (natAsObjCode n)

theorem natAsObjCode_zero_ne_succ (n : Nat) :
    natAsObjCode 0 ≠ natAsObjCode (n + 1) := by
  intro h
  cases h

theorem natAsObjCode_succ_injective {m n : Nat}
    (h : natAsObjCode (m + 1) = natAsObjCode (n + 1)) :
    natAsObjCode m = natAsObjCode n := by
  injection h with hInner

theorem nat_profile_zero :
    triAxisProjection (natAsObjCode 0) =
      { distinction := 0, time := 0, symmetry := 0 } :=
  rfl

theorem nat_profile_succ (n : Nat) :
    triAxisProjection (natAsObjCode (n + 1)) =
      TriAxisProfile.timeStep (triAxisProjection (natAsObjCode n)) :=
  rfl

theorem nat_profile (n : Nat) :
    (triAxisProjection (natAsObjCode n)).distinction = 0 ∧
      (triAxisProjection (natAsObjCode n)).time = n ∧
        (triAxisProjection (natAsObjCode n)).symmetry = 0 := by
  induction n with
  | zero =>
      exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      unfold natAsObjCode triAxisProjection TriAxisProfile.timeStep
      exact ⟨ih.left, congrArg Nat.succ ih.right.left, ih.right.right⟩

inductive SignedIntCode : Type where
  | zero : SignedIntCode
  | pos : Nat → SignedIntCode
  | neg : Nat → SignedIntCode
deriving Repr, DecidableEq

def signedIntNegate : SignedIntCode → SignedIntCode
  | SignedIntCode.zero => SignedIntCode.zero
  | SignedIntCode.pos n => SignedIntCode.neg n
  | SignedIntCode.neg n => SignedIntCode.pos n

def intAsObjCode : SignedIntCode → TriAxisObjCode
  | SignedIntCode.zero => natAsObjCode 0
  | SignedIntCode.pos n =>
      TriAxisObjCode.distinctionGen (natAsObjCode (n + 1))
  | SignedIntCode.neg n =>
      TriAxisObjCode.symmetryGen
        (TriAxisObjCode.distinctionGen (natAsObjCode (n + 1)))

theorem signedInt_negate_involutive (z : SignedIntCode) :
    signedIntNegate (signedIntNegate z) = z := by
  cases z <;> rfl

theorem int_profile_zero :
    triAxisProjection (intAsObjCode SignedIntCode.zero) =
      { distinction := 0, time := 0, symmetry := 0 } :=
  rfl

theorem int_profile_pos (n : Nat) :
    triAxisProjection (intAsObjCode (SignedIntCode.pos n)) =
      TriAxisProfile.distinctionStep (triAxisProjection (natAsObjCode (n + 1))) :=
  rfl

theorem int_profile_neg (n : Nat) :
    triAxisProjection (intAsObjCode (SignedIntCode.neg n)) =
      TriAxisProfile.symmetryStep
        (TriAxisProfile.distinctionStep
          (triAxisProjection (natAsObjCode (n + 1)))) :=
  rfl

theorem int_negative_has_symmetry (n : Nat) :
    (triAxisProjection (intAsObjCode (SignedIntCode.neg n))).symmetry = 1 := by
  unfold intAsObjCode triAxisProjection TriAxisProfile.symmetryStep
  exact congrArg Nat.succ (nat_profile (n + 1)).right.right

end BEDC.Foundations.TriangleGenerationSystem
