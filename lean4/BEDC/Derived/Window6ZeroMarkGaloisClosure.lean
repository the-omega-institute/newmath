namespace BEDC.Derived.Window6ZeroMarkGaloisClosure

/- Window6 zero-mark Galois closure is a proof-object for the order-theoretic
dilation-erosion adjunction at structuring size 6, distinct from count, gluing,
inequality, automaton-congruence, and signed-involution anchors. -/

inductive impliesList : List Bool → List Bool → Prop where
  | nil : impliesList [] []
  | cons {a b : Bool} {as bs : List Bool} :
      (a = true → b = true) → impliesList as bs → impliesList (a :: as) (b :: bs)

def force5 : List Bool → List Bool
  | _a :: _b :: _c :: _d :: _e :: rest => true :: true :: true :: true :: true :: rest
  | _a :: _b :: _c :: _d :: [] => [true, true, true, true]
  | _a :: _b :: _c :: [] => [true, true, true]
  | _a :: _b :: [] => [true, true]
  | _a :: [] => [true]
  | [] => []

def dilate6 : List Bool → List Bool
  | [] => [false, false, false, false, false]
  | false :: xs => false :: dilate6 xs
  | true :: xs => true :: force5 (dilate6 xs)

def and6 (a b c d e f : Bool) : Bool :=
  a && b && c && d && e && f

def erode6 : List Bool → List Bool
  | [] => []
  | p0 :: tail =>
      match tail with
      | [] => []
      | p1 :: tail1 =>
          match tail1 with
          | [] => []
          | p2 :: tail2 =>
              match tail2 with
              | [] => []
              | p3 :: tail3 =>
                  match tail3 with
                  | [] => []
                  | p4 :: tail4 =>
                      match tail4 with
                      | [] => []
                      | p5 :: rest =>
                          and6 p0 p1 p2 p3 p4 p5 ::
                            erode6 (p1 :: p2 :: p3 :: p4 :: p5 :: rest)

def Cl (S : List Bool) : List Bool := erode6 (dilate6 S)

def false_eq_true_elim {P : Sort u} : false = true → P := by
  intro h
  cases h

theorem nat_succ_inj {a b : Nat} : Nat.succ a = Nat.succ b → a = b :=
  fun h => Nat.noConfusion h (fun h2 => h2)

def zero_eq_succ_elim {n : Nat} {P : Sort u} : 0 = Nat.succ n → P := by
  intro h
  cases h

def succ_eq_zero_elim {n : Nat} {P : Sort u} : Nat.succ n = 0 → P := by
  intro h
  cases h

def five_eq_six_elim {P : Sort u} :
    (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))) =
      (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))))) → P := by
  intro h
  exact zero_eq_succ_elim
    (nat_succ_inj (nat_succ_inj (nat_succ_inj (nat_succ_inj (nat_succ_inj h)))))

def six_eq_five_elim {P : Sort u} :
    (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))))) =
      (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))) → P := by
  intro h
  exact succ_eq_zero_elim
    (nat_succ_inj (nat_succ_inj (nat_succ_inj (nat_succ_inj (nat_succ_inj h)))))

theorem impliesList_refl : ∀ S : List Bool, impliesList S S := by
  intro S
  induction S with
  | nil => exact impliesList.nil
  | cons x xs ih => exact impliesList.cons (fun h => h) ih

theorem impliesList_trans :
    ∀ A B C : List Bool, impliesList A B → impliesList B C → impliesList A C := by
  intro A
  induction A with
  | nil =>
      intro B C hAB hBC
      cases hAB
      cases hBC
      exact impliesList.nil
  | cons a as ih =>
      intro B C hAB hBC
      cases hAB with
      | cons hHeadAB hTailAB =>
          cases hBC with
          | cons hHeadBC hTailBC =>
              exact impliesList.cons (fun ha => hHeadBC (hHeadAB ha))
                (ih _ _ hTailAB hTailBC)

theorem impliesList_length_eq :
    ∀ A B : List Bool, impliesList A B → A.length = B.length := by
  intro A B h
  induction h with
  | nil => rfl
  | cons hHead hTail ih =>
      exact congrArg Nat.succ ih

theorem impliesList_antisymm :
    ∀ A B : List Bool, impliesList A B → impliesList B A → A = B := by
  intro A B hAB
  induction hAB with
  | nil =>
      intro hBA
      rfl
  | @cons a b as bs hHeadAB hTailAB ih =>
      intro hBA
      cases hBA with
      | cons hHeadBA hTailBA =>
          have headEq : a = b := by
            cases a
            · cases b
              · rfl
              · exact false_eq_true_elim (hHeadBA rfl)
            · cases b
              · exact false_eq_true_elim (hHeadAB rfl)
              · rfl
          have tailEq : as = bs := ih hTailBA
          cases headEq
          cases tailEq
          rfl

theorem force5_length : ∀ xs : List Bool, (force5 xs).length = xs.length := by
  intro xs
  cases xs with
  | nil => rfl
  | cons a xs1 =>
      cases xs1 with
      | nil => rfl
      | cons b xs2 =>
          cases xs2 with
          | nil => rfl
          | cons c xs3 =>
              cases xs3 with
              | nil => rfl
              | cons d xs4 =>
                  cases xs4 with
                  | nil => rfl
                  | cons e rest => rfl

theorem dilate6_length : ∀ S : List Bool, (dilate6 S).length = S.length + 5 := by
  intro S
  induction S with
  | nil => rfl
  | cons x xs ih =>
      cases x
      · change Nat.succ (dilate6 xs).length = Nat.succ (xs.length + 5)
        exact congrArg Nat.succ ih
      · have flen := force5_length (dilate6 xs)
        change Nat.succ (force5 (dilate6 xs)).length = Nat.succ (xs.length + 5)
        exact congrArg Nat.succ (flen.trans ih)

theorem and6_true_parts (a b c d e f : Bool) :
    and6 a b c d e f = true →
      a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true := by
  intro h
  cases a
  · cases h
  · cases b
    · cases h
    · cases c
      · cases h
      · cases d
        · cases h
        · cases e
          · cases h
          · cases f
            · cases h
            · exact And.intro rfl
                (And.intro rfl (And.intro rfl (And.intro rfl (And.intro rfl rfl))))

theorem and6_true_intro {a b c d e f : Bool} :
    a = true → b = true → c = true → d = true → e = true → f = true →
      and6 a b c d e f = true := by
  intro ha hb hc hd he hf
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  cases hf
  rfl

theorem impliesList_force5_left
    (D : List Bool) (p1 p2 p3 p4 p5 : Bool) (rest : List Bool) :
    impliesList (force5 D) (p1 :: p2 :: p3 :: p4 :: p5 :: rest) →
      p1 = true ∧ p2 = true ∧ p3 = true ∧ p4 = true ∧ p5 = true ∧
        impliesList D (p1 :: p2 :: p3 :: p4 :: p5 :: rest) := by
  intro h
  cases D with
  | nil => cases h
  | cons d1 D1 =>
      cases D1 with
      | nil =>
          cases h with
          | cons h1 ht1 => cases ht1
      | cons d2 D2 =>
          cases D2 with
          | nil =>
              cases h with
              | cons h1 ht1 =>
                  cases ht1 with
                  | cons h2 ht2 => cases ht2
          | cons d3 D3 =>
              cases D3 with
              | nil =>
                  cases h with
                  | cons h1 ht1 =>
                      cases ht1 with
                      | cons h2 ht2 =>
                          cases ht2 with
                          | cons h3 ht3 => cases ht3
              | cons d4 D4 =>
                  cases D4 with
                  | nil =>
                      cases h with
                      | cons h1 ht1 =>
                          cases ht1 with
                          | cons h2 ht2 =>
                              cases ht2 with
                              | cons h3 ht3 =>
                                  cases ht3 with
                                  | cons h4 ht4 => cases ht4
                  | cons d5 D5 =>
                      cases h with
                      | cons h1 ht1 =>
                          cases ht1 with
                          | cons h2 ht2 =>
                              cases ht2 with
                              | cons h3 ht3 =>
                                  cases ht3 with
                                  | cons h4 ht4 =>
                                      cases ht4 with
                                      | cons h5 ht5 =>
                                          exact And.intro (h1 rfl)
                                            (And.intro (h2 rfl)
                                              (And.intro (h3 rfl)
                                                (And.intro (h4 rfl)
                                                  (And.intro (h5 rfl)
                                                    (impliesList.cons (fun _ => h1 rfl)
                                                      (impliesList.cons (fun _ => h2 rfl)
                                                        (impliesList.cons (fun _ => h3 rfl)
                                                            (impliesList.cons (fun _ => h4 rfl)
                                                              (impliesList.cons (fun _ => h5 rfl)
                                                                ht5)))))))))

theorem impliesList_force5_right
    (D : List Bool) (p1 p2 p3 p4 p5 : Bool) (rest : List Bool) :
    p1 = true → p2 = true → p3 = true → p4 = true → p5 = true →
      impliesList D (p1 :: p2 :: p3 :: p4 :: p5 :: rest) →
        impliesList (force5 D) (p1 :: p2 :: p3 :: p4 :: p5 :: rest) := by
  intro hp1 hp2 hp3 hp4 hp5 hD
  cases D with
  | nil => cases hD
  | cons d1 D1 =>
      cases D1 with
      | nil =>
          cases hD with
          | cons hd1 ht1 => cases ht1
      | cons d2 D2 =>
          cases D2 with
          | nil =>
              cases hD with
              | cons hd1 ht1 =>
                  cases ht1 with
                  | cons hd2 ht2 => cases ht2
          | cons d3 D3 =>
              cases D3 with
              | nil =>
                  cases hD with
                  | cons hd1 ht1 =>
                      cases ht1 with
                      | cons hd2 ht2 =>
                          cases ht2 with
                          | cons hd3 ht3 => cases ht3
              | cons d4 D4 =>
                  cases D4 with
                  | nil =>
                      cases hD with
                      | cons hd1 ht1 =>
                          cases ht1 with
                          | cons hd2 ht2 =>
                              cases ht2 with
                              | cons hd3 ht3 =>
                                  cases ht3 with
                                  | cons hd4 ht4 => cases ht4
                  | cons d5 D5 =>
                      cases hD with
                      | cons hd1 ht1 =>
                          cases ht1 with
                          | cons hd2 ht2 =>
                              cases ht2 with
                              | cons hd3 ht3 =>
                                  cases ht3 with
                                  | cons hd4 ht4 =>
                                      cases ht4 with
                                      | cons hd5 ht5 =>
                                          exact impliesList.cons (fun _ => hp1)
                                            (impliesList.cons (fun _ => hp2)
                                              (impliesList.cons (fun _ => hp3)
                                                (impliesList.cons (fun _ => hp4)
                                                  (impliesList.cons (fun _ => hp5) ht5))))

inductive Pad5 : List Bool → List Bool → Prop where
  | nil (p0 p1 p2 p3 p4 : Bool) :
      Pad5 [] [p0, p1, p2, p3, p4]
  | cons {s p0 p1 p2 p3 p4 p5 : Bool} {S rest : List Bool} :
      Pad5 S (p1 :: p2 :: p3 :: p4 :: p5 :: rest) →
        Pad5 (s :: S) (p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: rest)

theorem pad5_of_length :
    ∀ S P : List Bool, P.length = S.length + 5 → Pad5 S P := by
  intro S
  induction S with
  | nil =>
      intro P h
      cases P with
      | nil => exact zero_eq_succ_elim h
      | cons p0 P1 =>
          cases P1 with
          | nil => exact zero_eq_succ_elim (nat_succ_inj h)
          | cons p1 P2 =>
              cases P2 with
              | nil => exact zero_eq_succ_elim (nat_succ_inj (nat_succ_inj h))
              | cons p2 P3 =>
                  cases P3 with
                  | nil => exact zero_eq_succ_elim (nat_succ_inj (nat_succ_inj (nat_succ_inj h)))
                  | cons p3 P4 =>
                      cases P4 with
                      | nil =>
                          exact zero_eq_succ_elim
                            (nat_succ_inj (nat_succ_inj (nat_succ_inj (nat_succ_inj h))))
                      | cons p4 P5 =>
                          cases P5 with
                          | nil => exact Pad5.nil p0 p1 p2 p3 p4
                          | cons p5 rest =>
                              cases rest with
                              | nil =>
                                  change
                                    (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))))) =
                                      (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))) at h
                                  exact six_eq_five_elim h
                              | cons r rs =>
                                  have hbad :=
                                    nat_succ_inj
                                      (nat_succ_inj
                                        (nat_succ_inj
                                          (nat_succ_inj
                                            (nat_succ_inj h))))
                                  exact succ_eq_zero_elim hbad
  | cons s S ih =>
      intro P h
      cases P with
      | nil => exact zero_eq_succ_elim h
      | cons p0 P1 =>
          cases P1 with
          | nil => exact zero_eq_succ_elim (nat_succ_inj h)
          | cons p1 P2 =>
              cases P2 with
              | nil => exact zero_eq_succ_elim (nat_succ_inj (nat_succ_inj h))
              | cons p2 P3 =>
                  cases P3 with
                  | nil => exact zero_eq_succ_elim (nat_succ_inj (nat_succ_inj (nat_succ_inj h)))
                  | cons p3 P4 =>
                      cases P4 with
                      | nil =>
                          exact zero_eq_succ_elim
                            (nat_succ_inj (nat_succ_inj (nat_succ_inj (nat_succ_inj h))))
                      | cons p4 P5 =>
                          cases P5 with
                          | nil =>
                              exact zero_eq_succ_elim
                                (nat_succ_inj
                                  (nat_succ_inj
                                    (nat_succ_inj
                                      (nat_succ_inj
                                        (nat_succ_inj h)))))
                          | cons p5 rest =>
                              have tailLen :
                                  (p1 :: p2 :: p3 :: p4 :: p5 :: rest).length = S.length + 5 :=
                                nat_succ_inj h
                              exact Pad5.cons (ih (p1 :: p2 :: p3 :: p4 :: p5 :: rest) tailLen)

theorem window6_galois_adjunction_pad5
    (S P : List Bool) (hpad : Pad5 S P) :
    impliesList (dilate6 S) P ↔ impliesList S (erode6 P) := by
  induction hpad with
  | nil p0 p1 p2 p3 p4 =>
      exact Iff.intro
        (fun _h => impliesList.nil)
        (fun _h =>
          impliesList.cons false_eq_true_elim
            (impliesList.cons false_eq_true_elim
              (impliesList.cons false_eq_true_elim
                (impliesList.cons false_eq_true_elim
                  (impliesList.cons false_eq_true_elim impliesList.nil)))))
  | @cons s p0 p1 p2 p3 p4 p5 S rest htail ih =>
      cases s
      · exact Iff.intro
          (fun h =>
            match h with
            | impliesList.cons _ ht => impliesList.cons false_eq_true_elim (ih.mp ht))
          (fun h =>
            match h with
            | impliesList.cons _ ht => impliesList.cons false_eq_true_elim (ih.mpr ht))
      · exact Iff.intro
          (fun h =>
            match h with
            | impliesList.cons h0 ht =>
                have tailData :=
                  impliesList_force5_left (dilate6 S) p1 p2 p3 p4 p5 rest ht
                have hD : impliesList (dilate6 S)
                    (p1 :: p2 :: p3 :: p4 :: p5 :: rest) :=
                  tailData.right.right.right.right.right
                have hE : impliesList S
                    (erode6 (p1 :: p2 :: p3 :: p4 :: p5 :: rest)) :=
                  ih.mp hD
                have hwin : and6 p0 p1 p2 p3 p4 p5 = true :=
                  and6_true_intro (h0 rfl) tailData.left
                    tailData.right.left tailData.right.right.left
                    tailData.right.right.right.left
                    tailData.right.right.right.right.left
                impliesList.cons (fun _ => hwin) hE)
          (fun h =>
            match h with
            | impliesList.cons h0 ht =>
                have hand : and6 p0 p1 p2 p3 p4 p5 = true := h0 rfl
                have parts := and6_true_parts p0 p1 p2 p3 p4 p5 hand
                have hD : impliesList (dilate6 S)
                    (p1 :: p2 :: p3 :: p4 :: p5 :: rest) :=
                  ih.mpr ht
                impliesList.cons (fun _ => parts.left)
                  (impliesList_force5_right (dilate6 S) p1 p2 p3 p4 p5 rest
                    parts.right.left
                    parts.right.right.left
                    parts.right.right.right.left
                    parts.right.right.right.right.left
                    parts.right.right.right.right.right hD))

theorem pad5_erode :
    ∀ S P : List Bool, Pad5 S P → Pad5 (erode6 P) P := by
  intro S P hpad
  induction hpad with
  | nil p0 p1 p2 p3 p4 =>
      exact Pad5.nil p0 p1 p2 p3 p4
  | @cons s p0 p1 p2 p3 p4 p5 S rest htail ih =>
      exact Pad5.cons ih

theorem window6_galois_adjunction
    (S P : List Bool) (hlen : P.length = S.length + 5) :
    impliesList (dilate6 S) P ↔ impliesList S (erode6 P) := by
  exact window6_galois_adjunction_pad5 S P (pad5_of_length S P hlen)

theorem window6_galois_adjunction_forward
    (S P : List Bool) (hlen : P.length = S.length + 5) :
    impliesList (dilate6 S) P → impliesList S (erode6 P) :=
  (window6_galois_adjunction S P hlen).mp

theorem window6_galois_adjunction_backward
    (S P : List Bool) (hlen : P.length = S.length + 5) :
    impliesList S (erode6 P) → impliesList (dilate6 S) P :=
  (window6_galois_adjunction S P hlen).mpr

theorem cl_extensive (S : List Bool) : impliesList S (Cl S) := by
  unfold Cl
  exact (window6_galois_adjunction S (dilate6 S) (dilate6_length S)).mp
    (impliesList_refl (dilate6 S))

theorem dilate6_monotone (S T : List Bool) (h : impliesList S T) :
    impliesList (dilate6 S) (dilate6 T) := by
  have hlenT : (dilate6 T).length = S.length + 5 := by
    exact (dilate6_length T).trans
      (congrArg (fun n => n + 5) (impliesList_length_eq S T h).symm)
  have hTClT : impliesList T (Cl T) := cl_extensive T
  exact (window6_galois_adjunction S (dilate6 T) hlenT).mpr
    (impliesList_trans S T (Cl T) h hTClT)

theorem erode6_monotone :
    ∀ P Q : List Bool, impliesList P Q → impliesList (erode6 P) (erode6 Q) := by
  intro P
  induction P with
  | nil =>
      intro Q h
      cases h
      exact impliesList.nil
  | cons p0 P1 ih =>
      intro Q h
      cases h with
      | cons h0 ht0 =>
          cases P1 with
          | nil =>
              cases ht0
              exact impliesList.nil
          | cons p1 P2 =>
              cases ht0 with
              | cons h1 ht1 =>
                  cases P2 with
                  | nil =>
                      cases ht1
                      exact impliesList.nil
                  | cons p2 P3 =>
                      cases ht1 with
                      | cons h2 ht2 =>
                          cases P3 with
                          | nil =>
                              cases ht2
                              exact impliesList.nil
                          | cons p3 P4 =>
                              cases ht2 with
                              | cons h3 ht3 =>
                                  cases P4 with
                                  | nil =>
                                      cases ht3
                                      exact impliesList.nil
                                  | cons p4 P5 =>
                                      cases ht3 with
                                      | cons h4 ht4 =>
                                          cases P5 with
                                          | nil =>
                                              cases ht4
                                              exact impliesList.nil
                                          | cons p5 prest =>
                                              cases ht4 with
                                              | cons h5 ht5 =>
                                                  have tailRel :=
                                                    impliesList.cons h1
                                                      (impliesList.cons h2
                                                        (impliesList.cons h3
                                                          (impliesList.cons h4
                                                            (impliesList.cons h5 ht5))))
                                                  exact impliesList.cons
                                                    (fun hp =>
                                                      have pp :=
                                                        and6_true_parts p0 p1 p2 p3 p4 p5 hp
                                                      and6_true_intro
                                                        (h0 pp.left)
                                                        (h1 pp.right.left)
                                                        (h2 pp.right.right.left)
                                                        (h3 pp.right.right.right.left)
                                                        (h4 pp.right.right.right.right.left)
                                                        (h5 pp.right.right.right.right.right))
                                                    (ih _ tailRel)

theorem cl_monotone (S T : List Bool) (h : impliesList S T) :
    impliesList (Cl S) (Cl T) := by
  unfold Cl
  exact erode6_monotone (dilate6 S) (dilate6 T) (dilate6_monotone S T h)

theorem dilate6_erode6_le
    (P : List Bool) (hlen : P.length = (erode6 P).length + 5) :
    impliesList (dilate6 (erode6 P)) P := by
  exact (window6_galois_adjunction (erode6 P) P hlen).mpr
    (impliesList_refl (erode6 P))

theorem dilate6_erode6_le_pad5
    (P : List Bool) (hpad : Pad5 (erode6 P) P) :
    impliesList (dilate6 (erode6 P)) P := by
  exact (window6_galois_adjunction_pad5 (erode6 P) P hpad).mpr
    (impliesList_refl (erode6 P))

theorem pad5_erode6_dilate6 (S : List Bool) : Pad5 (erode6 (dilate6 S)) (dilate6 S) := by
  exact pad5_erode S (dilate6 S) (pad5_of_length S (dilate6 S) (dilate6_length S))

theorem cl_idempotent_le (S : List Bool) : impliesList (Cl (Cl S)) (Cl S) := by
  unfold Cl
  exact erode6_monotone (dilate6 (erode6 (dilate6 S))) (dilate6 S)
    (dilate6_erode6_le_pad5 (dilate6 S) (pad5_erode6_dilate6 S))

theorem cl_idempotent (S : List Bool) :
    impliesList (Cl (Cl S)) (Cl S) ∧ impliesList (Cl S) (Cl (Cl S)) := by
  exact And.intro (cl_idempotent_le S) (cl_extensive (Cl S))

def notList : List Bool → List Bool
  | [] => []
  | x :: xs => (!x) :: notList xs

def Zmarks (w : List Bool) : List Bool := erode6 (notList w)

theorem erode6_image_closed_window
    (P : List Bool) (hlen : P.length = (erode6 P).length + 5) :
    impliesList (Cl (erode6 P)) (erode6 P) ∧
      impliesList (erode6 P) (Cl (erode6 P)) := by
  apply And.intro
  · unfold Cl
    exact erode6_monotone (dilate6 (erode6 P)) P (dilate6_erode6_le P hlen)
  · exact cl_extensive (erode6 P)

theorem window6_Zmarks_closed_concrete_m6 (a b c d e f : Bool) :
    Cl (Zmarks [a, b, c, d, e, f]) = Zmarks [a, b, c, d, e, f] := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

theorem window6_Zmarks_closed_concrete_m7 (a b c d e f g : Bool) :
    Cl (Zmarks [a, b, c, d, e, f, g]) = Zmarks [a, b, c, d, e, f, g] := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

def boolEq (a b : Bool) : Bool :=
  match a, b with
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

def listBoolEq : List Bool → List Bool → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => boolEq a b && listBoolEq as bs

def prependAll (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | w :: ws => (b :: w) :: prependAll b ws

def appendLists : List (List Bool) → List (List Bool) → List (List Bool)
  | [], ys => ys
  | x :: xs, ys => x :: appendLists xs ys

def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => appendLists (prependAll false (boolWords n)) (prependAll true (boolWords n))

def boolToNat : Bool → Nat
  | false => 0
  | true => 1

def countClosed : List (List Bool) → Nat
  | [] => 0
  | w :: ws => boolToNat (listBoolEq (Cl w) w) + countClosed ws

def closedCount (n : Nat) : Nat := countClosed (boolWords n)

theorem closedCount_1 : closedCount 1 = 2 := by
  rfl

theorem closedCount_2 : closedCount 2 = 4 := by
  rfl

theorem closedCount_3 : closedCount 3 = 7 := by
  rfl

theorem closedCount_4 : closedCount 4 = 11 := by
  rfl

theorem closedCount_5 : closedCount 5 = 16 := by
  rfl

theorem closedCount_6 : closedCount 6 = 22 := by
  rfl

theorem erode6_all_true_singleton :
    erode6 [true, true, true, true, true, true] = [true] := by
  rfl

theorem cl_single_mark_left :
    Cl [true, false, false, false, false, false] =
      [true, false, false, false, false, false] := by
  rfl

theorem cl_adjacent_marks_fill :
    Cl [true, false, true] = [true, true, true] := by
  rfl

end BEDC.Derived.Window6ZeroMarkGaloisClosure
