import BEDC.Derived.GoldenMeanShiftUp

namespace BEDC.Derived.AxisZeckendorf.InverseLimitLifting

abbrev Bit : Type :=
  BEDC.Derived.GoldenMeanShiftUp.Bit

abbrev GoldenStepBit : Bit -> Bit -> Prop :=
  BEDC.Derived.GoldenMeanShiftUp.allowedPair

def zeroBit : Bit :=
  BEDC.Derived.GoldenMeanShiftUp.Bit.zero

structure GoldenWord where
  bits : List Bit
  no11_at :
    (k : Nat) -> (hk : k + 1 < bits.length) ->
      GoldenStepBit
        (bits.get ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩)
        (bits.get ⟨k + 1, hk⟩)

def bitsFrom (bit : Nat -> Bit) (start : Nat) : Nat -> List Bit
  | 0 => []
  | n + 1 => bit start :: bitsFrom bit (start + 1) n

theorem bitsFrom_length (bit : Nat -> Bit) (start n : Nat) :
    (bitsFrom bit start n).length = n := by
  induction n generalizing start with
  | zero =>
      rfl
  | succ n ih =>
      change Nat.succ (bitsFrom bit (start + 1) n).length = Nat.succ n
      exact congrArg Nat.succ (ih (start + 1))

theorem bitsFrom_get (bit : Nat -> Bit) (start n k : Nat) (hk : k < n) :
    (bitsFrom bit start n).get
        ⟨k, by
          rw [bitsFrom_length bit start n]
          exact hk⟩ =
      bit (start + k) := by
  induction n generalizing start k with
  | zero =>
      exact False.elim (Nat.not_lt_zero k hk)
  | succ n ih =>
      cases k with
      | zero =>
          change bit start = bit (start + 0)
          rw [Nat.add_zero]
      | succ k =>
          have htail : k < n := Nat.lt_of_succ_lt_succ hk
          change
            (bitsFrom bit (start + 1) n).get
                ⟨k, by
                  rw [bitsFrom_length bit (start + 1) n]
                  exact htail⟩ =
              bit (start + (k + 1))
          rw [ih (start + 1) k htail]
          rw [Nat.add_assoc, Nat.add_comm 1 k]

structure GoldenPrefix (n : Nat) where
  bitAt : Nat -> Bit
  no11_at :
    (k : Nat) -> (hk : k + 1 < n) ->
      GoldenStepBit (bitAt k) (bitAt (k + 1))

def GoldenPrefix.word {n : Nat} (pref : GoldenPrefix n) : GoldenWord :=
  {
    bits := bitsFrom pref.bitAt 0 n
    no11_at := by
      intro k hk
      have hkLevel : k + 1 < n := by
        rw [bitsFrom_length pref.bitAt 0 n] at hk
        exact hk
      have hkLeft : k < n :=
        Nat.lt_trans (Nat.lt_succ_self k) hkLevel
      rw [bitsFrom_get pref.bitAt 0 n k hkLeft]
      rw [bitsFrom_get pref.bitAt 0 n (k + 1) hkLevel]
      rw [Nat.zero_add, Nat.zero_add]
      exact pref.no11_at k hkLevel
  }

theorem GoldenPrefix.word_bits_length {n : Nat} (pref : GoldenPrefix n) :
    pref.word.bits.length = n := by
  exact bitsFrom_length pref.bitAt 0 n

def GoldenPrefix.get {n : Nat} (pref : GoldenPrefix n)
    (k : Nat) (_hk : k < n) : Bit :=
  pref.bitAt k

theorem GoldenPrefix.get_irrel {n : Nat} (pref : GoldenPrefix n)
    (k : Nat) (hk hk' : k < n) :
    pref.get k hk = pref.get k hk' := by
  rfl

theorem GoldenPrefix.word_get {n : Nat} (pref : GoldenPrefix n)
    (k : Nat) (hk : k < n) :
    pref.word.bits.get
        ⟨k, by
          rw [pref.word_bits_length]
          exact hk⟩ =
      pref.get k hk := by
  unfold GoldenPrefix.word GoldenPrefix.get
  rw [bitsFrom_get pref.bitAt 0 n k hk]
  rw [Nat.zero_add]

theorem GoldenPrefix.step_at {n : Nat} (pref : GoldenPrefix n)
    (k : Nat) (hk : k + 1 < n) :
    GoldenStepBit
      (pref.get k (Nat.lt_trans (Nat.lt_succ_self k) hk))
      (pref.get (k + 1) hk) := by
  exact pref.no11_at k hk

def prefixReadBelow {n : Nat} (pref : GoldenPrefix (n + 1)) (k : Nat) : Bit :=
  if h : k < n then
    pref.get k (Nat.lt_trans h (Nat.lt_succ_self n))
  else
    zeroBit

theorem prefixReadBelow_visible {n : Nat} (pref : GoldenPrefix (n + 1))
    (k : Nat) (hk : k < n) :
    prefixReadBelow pref k =
      pref.get k (Nat.lt_trans hk (Nat.lt_succ_self n)) := by
  unfold prefixReadBelow
  rw [dif_pos hk]

def truncatePrefix {n : Nat} (pref : GoldenPrefix (n + 1)) :
    GoldenPrefix n :=
  {
    bitAt := prefixReadBelow pref
    no11_at := by
      intro k hk
      rw [prefixReadBelow_visible pref k
        (Nat.lt_trans (Nat.lt_succ_self k) hk)]
      rw [prefixReadBelow_visible pref (k + 1) hk]
      exact pref.step_at k (Nat.lt_trans hk (Nat.lt_succ_self n))
  }

theorem truncatePrefix_get {n : Nat} (pref : GoldenPrefix (n + 1))
    (k : Nat) (hk : k < n) :
    (truncatePrefix pref).get k hk =
      pref.get k (Nat.lt_trans hk (Nat.lt_succ_self n)) := by
  exact prefixReadBelow_visible pref k hk

structure GoldenPrefixTower where
  prefixAt : (n : Nat) -> GoldenPrefix n
  compatible :
    (n k : Nat) -> (hk : k < n) ->
      (truncatePrefix (prefixAt (n + 1))).get k hk =
        (prefixAt n).get k hk

structure GoldenStream where
  bit : Nat -> Bit
  no11_at : (n : Nat) -> GoldenStepBit (bit n) (bit (n + 1))

def streamToPrefix (stream : GoldenStream) (n : Nat) : GoldenPrefix n :=
  {
    bitAt := stream.bit
    no11_at := fun k _hk => stream.no11_at k
  }

theorem streamToPrefix_get (stream : GoldenStream) (n k : Nat)
    (hk : k < n) :
    (streamToPrefix stream n).get k hk = stream.bit k := by
  rfl

def streamToTower (stream : GoldenStream) : GoldenPrefixTower :=
  {
    prefixAt := streamToPrefix stream
    compatible := by
      intro n k hk
      rw [truncatePrefix_get]
      rfl
  }

theorem tower_prefix_get_succ {tower : GoldenPrefixTower}
    (n k : Nat) (hk : k < n) :
    (tower.prefixAt n).get k hk =
      (tower.prefixAt (n + 1)).get k
        (Nat.lt_trans hk (Nat.lt_succ_self n)) := by
  have htruncate :=
    truncatePrefix_get (tower.prefixAt (n + 1)) k hk
  have hcompat := tower.compatible n k hk
  exact Eq.trans (Eq.symm hcompat) htruncate

theorem tower_prefix_bit_extend_by {tower : GoldenPrefixTower}
    (extra n k : Nat) (hk : k < n) :
    (tower.prefixAt n).bitAt k =
      (tower.prefixAt (n + extra)).bitAt k := by
  induction extra with
  | zero =>
      rfl
  | succ extra ih =>
      have step :
          (tower.prefixAt (n + extra)).bitAt k =
            (tower.prefixAt (n + extra + 1)).bitAt k :=
        tower_prefix_get_succ (tower := tower) (n + extra) k
          (Nat.lt_of_lt_of_le hk (Nat.le_add_right n extra))
      exact Eq.trans ih step

theorem tower_prefix_get_from_successor {tower : GoldenPrefixTower}
    (n k : Nat) (hk : k < n) :
    (tower.prefixAt (k + 1)).get k (Nat.lt_succ_self k) =
      (tower.prefixAt n).get k hk := by
  induction hk with
  | refl =>
      rfl
  | step hk ih =>
      have stepEq :
          (tower.prefixAt _).get k hk =
            (tower.prefixAt (_ + 1)).get k (Nat.lt_succ_of_lt hk) := by
        exact tower_prefix_get_succ (tower := tower) _ k hk
      exact Eq.trans ih stepEq

def towerToStream (tower : GoldenPrefixTower) : GoldenStream :=
  {
    bit := fun k => (tower.prefixAt (k + 1)).get k (Nat.lt_succ_self k)
    no11_at := by
      intro k
      have hfirst :
          (tower.prefixAt (k + 1)).get k (Nat.lt_succ_self k) =
            (tower.prefixAt (k + 2)).get k
              (Nat.lt_trans (Nat.lt_succ_self k) (Nat.lt_succ_self (k + 1))) := by
        exact tower_prefix_get_succ (tower := tower) (k + 1) k
          (Nat.lt_succ_self k)
      rw [hfirst]
      exact (tower.prefixAt (k + 2)).step_at k (Nat.lt_succ_self (k + 1))
  }

theorem tower_stream_readback_pointwise_get
    (tower : GoldenPrefixTower) (n k : Nat) (hk : k < n) :
    ((streamToTower (towerToStream tower)).prefixAt n).get k hk =
      (tower.prefixAt n).get k hk := by
  exact tower_prefix_get_from_successor (tower := tower) n k hk

theorem tower_stream_readback_pointwise
    (tower : GoldenPrefixTower) (n k : Nat) (hk : k < n) :
    ((streamToTower (towerToStream tower)).prefixAt n).word.bits.get
        ⟨k, by
          rw [((streamToTower (towerToStream tower)).prefixAt n).word_bits_length]
          exact hk⟩ =
      (tower.prefixAt n).word.bits.get
        ⟨k, by
          rw [(tower.prefixAt n).word_bits_length]
          exact hk⟩ := by
  rw [GoldenPrefix.word_get]
  rw [GoldenPrefix.word_get]
  exact tower_stream_readback_pointwise_get tower n k hk

end BEDC.Derived.AxisZeckendorf.InverseLimitLifting
