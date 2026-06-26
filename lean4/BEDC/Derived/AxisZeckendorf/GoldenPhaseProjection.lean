import BEDC.Derived.ZeckendorfUp

namespace BEDC.Derived.AxisZeckendorf.GoldenPhaseProjection

abbrev zeckendorf : Nat -> List Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorf

abbrev zeckendorfValue : List Nat -> Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorfValue

abbrev ZeckendorfBelow : Nat -> List Nat -> Prop :=
  BEDC.Derived.ZeckendorfUp.ZeckendorfBelow

inductive Bit where
  | zero
  | one

def bitOfIdxsAt : List Nat -> Nat -> Bit
  | [], _ => Bit.zero
  | index :: rest, k =>
      if index = k then Bit.one else bitOfIdxsAt rest k

def zeroBits : Nat -> List Bit
  | 0 => []
  | width + 1 => Bit.zero :: zeroBits width

def bitsOfIdxsBelow : List Nat -> Nat -> List Bit
  | _, 0 => []
  | [], width => zeroBits width
  | index :: rest, top + 1 =>
      if index = top then
        match top with
        | 0 => [Bit.one]
        | lower + 1 => Bit.one :: Bit.zero :: bitsOfIdxsBelow rest lower
      else
        Bit.zero :: bitsOfIdxsBelow (index :: rest) top

def ZeckBitsOf (n width : Nat) : List Bit :=
  bitsOfIdxsBelow (zeckendorf n) width

inductive NoAdjacentOne : List Bit -> Prop where
  | nil : NoAdjacentOne []
  | zero_cons {bits : List Bit} :
      NoAdjacentOne bits -> NoAdjacentOne (Bit.zero :: bits)
  | one_nil : NoAdjacentOne [Bit.one]
  | one_zero {bits : List Bit} :
      NoAdjacentOne bits -> NoAdjacentOne (Bit.one :: Bit.zero :: bits)

def indicesOfBitsFrom : Nat -> List Bit -> List Nat
  | _, [] => []
  | top, Bit.zero :: rest =>
      match top with
      | 0 => indicesOfBitsFrom 0 rest
      | lower + 1 => indicesOfBitsFrom lower rest
  | top, Bit.one :: rest =>
      top ::
        match top with
        | 0 => indicesOfBitsFrom 0 rest
        | lower + 1 => indicesOfBitsFrom lower rest

def indicesOfBitsOfBound : Nat -> List Bit -> List Nat
  | 0, _ => []
  | top + 1, bits => indicesOfBitsFrom top bits

def indicesOfBits (bits : List Bit) : List Nat :=
  indicesOfBitsOfBound bits.length bits

def ReadbackBits (bits : List Bit) : Nat :=
  zeckendorfValue (indicesOfBits bits)

def ZeckendorfWidthCovers (n width : Nat) : Prop :=
  ZeckendorfBelow width (zeckendorf n)

abbrev enoughWidth (n width : Nat) : Prop :=
  ZeckendorfWidthCovers n width

theorem zeroBits_no11 (width : Nat) :
    NoAdjacentOne (zeroBits width) := by
  induction width with
  | zero =>
      exact NoAdjacentOne.nil
  | succ width ih =>
      exact NoAdjacentOne.zero_cons ih

theorem nat_lt_succ_succ (n : Nat) :
    n < n + 1 + 1 := by
  exact Nat.lt_trans (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1))

theorem bitsOfIdxsBelow_no11_from_repr (width : Nat) :
    forall (indices : List Nat) (bound : Nat),
      BEDC.Derived.Window6Zeckendorf.ZReprBelow bound indices ->
        NoAdjacentOne (bitsOfIdxsBelow indices width)
    := by
  exact Nat.strongRecOn width
    (motive := fun w =>
      forall (indices : List Nat) (bound : Nat),
        BEDC.Derived.Window6Zeckendorf.ZReprBelow bound indices ->
          NoAdjacentOne (bitsOfIdxsBelow indices w))
    (fun w ih => by
      intro indices bound h
      cases w with
      | zero =>
          exact NoAdjacentOne.nil
      | succ top =>
          cases indices with
          | nil =>
              exact zeroBits_no11 (top + 1)
          | cons index rest =>
              cases h with
              | cons hlt htail =>
                  unfold bitsOfIdxsBelow
                  by_cases heq : index = top
                  · rw [if_pos heq]
                    cases top with
                    | zero =>
                        exact NoAdjacentOne.one_nil
                    | succ lower =>
                        have htailBelow :
                            BEDC.Derived.Window6Zeckendorf.ZReprBelow lower rest := by
                          rw [heq] at htail
                          exact htail
                        exact NoAdjacentOne.one_zero
                          (ih lower (nat_lt_succ_succ lower) rest lower htailBelow)
                  · rw [if_neg heq]
                    exact NoAdjacentOne.zero_cons
                      (ih top (Nat.lt_succ_self top) (index :: rest) bound
                        (BEDC.Derived.Window6Zeckendorf.ZReprBelow.cons hlt htail)))

theorem zeck_bits_no11 (n width : Nat) :
    NoAdjacentOne (ZeckBitsOf n width) := by
  unfold ZeckBitsOf
  have hbelow : ZeckendorfBelow (n + 2) (zeckendorf n) :=
    (BEDC.Derived.ZeckendorfUp.zeckendorf_spec n).left
  exact bitsOfIdxsBelow_no11_from_repr width (zeckendorf n) (n + 2) hbelow

theorem zeroBits_length (width : Nat) :
    (zeroBits width).length = width := by
  induction width with
  | zero =>
      rfl
  | succ width ih =>
      rw [zeroBits, List.length_cons, ih]

theorem bitsOfIdxsBelow_length (indices : List Nat) (width : Nat) :
    (bitsOfIdxsBelow indices width).length = width := by
  exact (Nat.strongRecOn width
    (motive := fun w =>
      forall indices : List Nat, (bitsOfIdxsBelow indices w).length = w)
    (fun w ih => by
      intro indices
      cases w with
      | zero =>
          cases indices <;> rfl
      | succ top =>
          cases indices with
          | nil =>
              exact zeroBits_length (top + 1)
          | cons index rest =>
              unfold bitsOfIdxsBelow
              by_cases h : index = top
              · rw [if_pos h]
                cases top with
                | zero =>
                    rfl
                | succ lower =>
                    rw [List.length_cons, List.length_cons,
                      ih lower (nat_lt_succ_succ lower) rest]
              · rw [if_neg h, List.length_cons,
                  ih top (Nat.lt_succ_self top) (index :: rest)])) indices

theorem indicesOfBitsFrom_zeroBits (top width : Nat) :
    indicesOfBitsFrom top (zeroBits width) = [] := by
  induction width generalizing top with
  | zero =>
      rfl
  | succ width ih =>
      cases top with
      | zero =>
          exact ih 0
      | succ lower =>
          exact ih lower

theorem indicesOfBitsFrom_zero_cons_bitsBelow
    (top : Nat) (indices : List Nat) :
    indicesOfBitsFrom top (Bit.zero :: bitsOfIdxsBelow indices top) =
      indicesOfBitsOfBound top (bitsOfIdxsBelow indices top) := by
  cases top <;> rfl

theorem indicesOfBitsOfBound_bitsOfIdxsBelow_exact (width : Nat) :
    forall (indices : List Nat),
      BEDC.Derived.Window6Zeckendorf.ZReprBelow width indices ->
        indicesOfBitsOfBound width (bitsOfIdxsBelow indices width) = indices
    := by
  exact Nat.strongRecOn width
    (motive := fun w =>
      forall indices : List Nat,
        BEDC.Derived.Window6Zeckendorf.ZReprBelow w indices ->
          indicesOfBitsOfBound w (bitsOfIdxsBelow indices w) = indices)
    (fun w ih => by
      intro indices h
      cases w with
      | zero =>
          cases indices with
          | nil =>
              rfl
          | cons index rest =>
              cases h with
              | cons hlt _ =>
                  exact False.elim (Nat.not_lt_zero index hlt)
      | succ top =>
          cases indices with
          | nil =>
              change indicesOfBitsFrom top (zeroBits (top + 1)) = []
              exact indicesOfBitsFrom_zeroBits top (top + 1)
          | cons index rest =>
              cases h with
              | cons hlt htail =>
                  unfold indicesOfBitsOfBound bitsOfIdxsBelow
                  by_cases heq : index = top
                  · rw [if_pos heq]
                    cases top with
                    | zero =>
                        have htailBelow :
                            BEDC.Derived.Window6Zeckendorf.ZReprBelow 0 rest := by
                          rw [heq] at htail
                          exact htail
                        have tailExact :
                            indicesOfBitsOfBound 0 (bitsOfIdxsBelow rest 0) = rest :=
                          ih 0 (Nat.zero_lt_succ 0) rest htailBelow
                        rw [heq]
                        change [0] = 0 :: rest
                        rw [<- tailExact]
                        rfl
                    | succ lower =>
                        have htailBelow :
                            BEDC.Derived.Window6Zeckendorf.ZReprBelow lower rest := by
                          rw [heq] at htail
                          exact htail
                        have tailExact :
                            indicesOfBitsOfBound lower
                                (bitsOfIdxsBelow rest lower) = rest :=
                          ih lower (nat_lt_succ_succ lower) rest htailBelow
                        change
                          (lower + 1) ::
                              indicesOfBitsFrom lower
                                (Bit.zero :: bitsOfIdxsBelow rest lower) =
                            index :: rest
                        rw [heq, indicesOfBitsFrom_zero_cons_bitsBelow lower rest, tailExact]
                  · rw [if_neg heq]
                    have hle : index <= top := Nat.le_of_lt_succ hlt
                    have hltTop : index < top := Nat.lt_of_le_of_ne hle heq
                    have hbelow :
                        BEDC.Derived.Window6Zeckendorf.ZReprBelow top (index :: rest) :=
                      BEDC.Derived.Window6Zeckendorf.ZReprBelow.cons hltTop htail
                    have tailExact :
                        indicesOfBitsOfBound top
                            (bitsOfIdxsBelow (index :: rest) top) = index :: rest :=
                      ih top (Nat.lt_succ_self top) (index :: rest) hbelow
                    change
                      indicesOfBitsFrom top
                          (Bit.zero :: bitsOfIdxsBelow (index :: rest) top) =
                        index :: rest
                    rw [indicesOfBitsFrom_zero_cons_bitsBelow top (index :: rest), tailExact])

theorem indicesOfBits_bitsOfIdxsBelow_exact
    (width : Nat) (indices : List Nat)
    (h : BEDC.Derived.Window6Zeckendorf.ZReprBelow width indices) :
    indicesOfBits (bitsOfIdxsBelow indices width) = indices := by
  unfold indicesOfBits
  rw [bitsOfIdxsBelow_length indices width]
  exact indicesOfBitsOfBound_bitsOfIdxsBelow_exact width indices h

theorem zeck_bits_readback (n width : Nat)
    (h : enoughWidth n width) :
    ReadbackBits (ZeckBitsOf n width) = n := by
  unfold ReadbackBits ZeckBitsOf
  rw [indicesOfBits_bitsOfIdxsBelow_exact width (zeckendorf n) h]
  exact BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore n

end BEDC.Derived.AxisZeckendorf.GoldenPhaseProjection
