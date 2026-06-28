import BEDC.Derived.RHRoute.FarEndUnityNormalization
import BEDC.Derived.ZeckendorfUp

namespace BEDC.Derived.RHRoute.ZeckendorfSolenoidSelector

abbrev Rat :=
  BEDC.Derived.RationalUp.RatNum

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindow

abbrev PrimeLocalChannel :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeLocalChannel

abbrev FarEndUnityNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.FarEndUnityNormalization

def zeckendorfIndices (n : Nat) : List Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorf n

def zeckendorfFiniteIndexBit (n index : Nat) : Bool :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.listMemNat index (zeckendorfIndices n)

theorem zeckendorfFiniteIndexBit_true {n index : Nat} :
    zeckendorfFiniteIndexBit n index = true ->
      index ∈ zeckendorfIndices n := by
  intro selected
  exact BEDC.Derived.RHRoute.FinitePrimeWindow.listMemNat_true selected

theorem zeckendorfFiniteIndexBit_of_mem {n index : Nat} :
    index ∈ zeckendorfIndices n ->
      zeckendorfFiniteIndexBit n index = true := by
  intro member
  exact BEDC.Derived.RHRoute.FinitePrimeWindow.listMemNat_of_mem member

theorem zeckendorfFiniteIndexBit_false_not_mem {n index : Nat} :
    zeckendorfFiniteIndexBit n index = false ->
      Not (index ∈ zeckendorfIndices n) := by
  intro absent
  exact BEDC.Derived.RHRoute.FinitePrimeWindow.listMemNat_false_not_mem absent

theorem zeckendorfIndices_legal (n : Nat) :
    BEDC.Derived.ZeckendorfUp.ZeckendorfLegal (zeckendorfIndices n) := by
  exact BEDC.Derived.ZeckendorfUp.zeckendorf_legal n

theorem zeckendorfIndices_sum_restore (n : Nat) :
    BEDC.Derived.ZeckendorfUp.zeckendorfValue (zeckendorfIndices n) = n := by
  exact BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore n

/--
有限 Zeckendorf 选择子路线。本结构不构造无限 solenoid 或远端点；
它只把有限 Zeckendorf index 读成 FarEnd 归一化源窗口中的素坐标。
-/
structure ZeckendorfSolenoidSelectorRoute where
  farEnd : FarEndUnityNormalization
  fallbackPrime : Nat
  fallback_mem : farEnd.primeWindow.sourceWindow.mem fallbackPrime

def ZeckendorfSolenoidSelectorRoute.sourceWindow
    (route : ZeckendorfSolenoidSelectorRoute) : PrimeWindow :=
  route.farEnd.primeWindow.sourceWindow

def ZeckendorfSolenoidSelectorRoute.normalizedChannel
    (route : ZeckendorfSolenoidSelectorRoute) : PrimeLocalChannel :=
  route.farEnd.primeWindow.normalizedChannel

def finiteSourceSelector (fallback : Nat) : List Nat -> Nat -> Nat
  | [], _index => fallback
  | prime :: _rest, 0 => prime
  | _prime :: rest, index + 1 => finiteSourceSelector fallback rest index

theorem finiteSourceSelector_mem_or_fallback (fallback : Nat) :
    forall (xs : List Nat) (index : Nat),
      finiteSourceSelector fallback xs index ∈ xs ∨
        finiteSourceSelector fallback xs index = fallback
  | [], _index => by
      exact Or.inr rfl
  | prime :: rest, 0 => by
      exact Or.inl (List.Mem.head rest)
  | prime :: rest, index + 1 => by
      have selected := finiteSourceSelector_mem_or_fallback fallback rest index
      cases selected with
      | inl member =>
          exact Or.inl (List.Mem.tail prime member)
      | inr fallbackEq =>
          exact Or.inr fallbackEq

def zeckendorfSolenoidPrime
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) : Nat :=
  finiteSourceSelector route.fallbackPrime route.sourceWindow.elems index

theorem zeckendorfSolenoidPrime_selector_scope
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) :
    zeckendorfSolenoidPrime route index ∈ route.sourceWindow.elems ∨
      zeckendorfSolenoidPrime route index = route.fallbackPrime := by
  unfold zeckendorfSolenoidPrime
  exact finiteSourceSelector_mem_or_fallback
    route.fallbackPrime route.sourceWindow.elems index

def zeckendorfSolenoidCoordinate
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) : Rat :=
  BEDC.Derived.RHRoute.UnitaryBalance.channelAmplitude
    route.normalizedChannel (zeckendorfSolenoidPrime route index)

def zeckendorfSolenoidPrimeReadback
    (route : ZeckendorfSolenoidSelectorRoute) (n : Nat) : List Nat :=
  List.map (zeckendorfSolenoidPrime route) (zeckendorfIndices n)

def zeckendorfSolenoidCoordinateReadback
    (route : ZeckendorfSolenoidSelectorRoute) (n : Nat) : List Rat :=
  List.map (zeckendorfSolenoidCoordinate route) (zeckendorfIndices n)

theorem zeckendorfSolenoidCoordinate_eq_channelAmplitude
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) :
    zeckendorfSolenoidCoordinate route index =
      BEDC.Derived.RHRoute.UnitaryBalance.channelAmplitude
        route.normalizedChannel (zeckendorfSolenoidPrime route index) := by
  rfl

theorem zeckendorfSolenoidPrime_source_mem
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) :
    route.sourceWindow.mem (zeckendorfSolenoidPrime route index) := by
  have selected := zeckendorfSolenoidPrime_selector_scope route index
  cases selected with
  | inl member =>
      exact member
  | inr fallbackEq =>
      rw [fallbackEq]
      exact route.fallback_mem

theorem zeckendorfSolenoidPrime_is_prime
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) :
    BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime
      (zeckendorfSolenoidPrime route index) := by
  exact BEDC.Derived.RHRoute.FinitePrimeWindow.All.mem
    route.sourceWindow.all_prime
    (zeckendorfSolenoidPrime_source_mem route index)

theorem zeckendorfSolenoidPrime_normalized_mem
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) :
    route.normalizedChannel.window.mem (zeckendorfSolenoidPrime route index) := by
  have sourceMember :
      route.farEnd.primeWindow.sourceWindow.mem
        (zeckendorfSolenoidPrime route index) :=
    zeckendorfSolenoidPrime_source_mem route index
  unfold ZeckendorfSolenoidSelectorRoute.normalizedChannel
  rw [route.farEnd.primeWindow.window_preserved]
  exact sourceMember

theorem zeckendorfSolenoidPrime_den_pos
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat) :
    0 < route.normalizedChannel.amp_den
      (zeckendorfSolenoidPrime route index) := by
  exact route.farEnd.primeWindow.den_pos_on_source_window
    (zeckendorfSolenoidPrime route index)
    (zeckendorfSolenoidPrime_source_mem route index)

theorem zeckendorfSolenoidSelector_unit_norm
    (route : ZeckendorfSolenoidSelectorRoute) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        route.normalizedChannel)
      BEDC.Derived.RationalUp.ratOne := by
  exact route.farEnd.primeWindow.unit_norm_transfers

theorem zeckendorfSolenoidSelector_far_end_not_internalized
    (route : ZeckendorfSolenoidSelectorRoute) :
    BEDC.Derived.TranscendentalFarEndUp.farEndSocketElementProjection
      BEDC.Derived.LocatedReal.RatMetricKitConcrete
      route.farEnd.socket = none := by
  exact route.farEnd.far_end_not_internalized

private theorem selectedPrime_mem_map_of_mem
    (route : ZeckendorfSolenoidSelectorRoute) :
    forall {indices : List Nat} {index : Nat},
      index ∈ indices ->
        zeckendorfSolenoidPrime route index ∈
          List.map (zeckendorfSolenoidPrime route) indices
  | [], _index, member => by
      cases member
  | head :: tail, index, member => by
      cases member with
      | head =>
          exact List.Mem.head (List.map (zeckendorfSolenoidPrime route) tail)
      | tail _ tailMember =>
          exact List.Mem.tail (zeckendorfSolenoidPrime route head)
            (selectedPrime_mem_map_of_mem route tailMember)

private theorem selectedPrime_source_mem_from_list
    (route : ZeckendorfSolenoidSelectorRoute) :
    forall {indices : List Nat} {prime : Nat},
      prime ∈ List.map (zeckendorfSolenoidPrime route) indices ->
        route.sourceWindow.mem prime
  | [], _prime, member => by
      cases member
  | index :: rest, _prime, member => by
      cases member with
      | head =>
          exact zeckendorfSolenoidPrime_source_mem route index
      | tail _ tailMember =>
          exact selectedPrime_source_mem_from_list route tailMember

theorem zeckendorfSolenoidPrimeReadback_of_bit_true
    (route : ZeckendorfSolenoidSelectorRoute) {n index : Nat} :
    zeckendorfFiniteIndexBit n index = true ->
      zeckendorfSolenoidPrime route index ∈
        zeckendorfSolenoidPrimeReadback route n := by
  intro selected
  unfold zeckendorfSolenoidPrimeReadback
  exact selectedPrime_mem_map_of_mem route
    (zeckendorfFiniteIndexBit_true selected)

theorem zeckendorfSolenoidReadbackPrime_source_mem
    (route : ZeckendorfSolenoidSelectorRoute) {n prime : Nat} :
    prime ∈ zeckendorfSolenoidPrimeReadback route n ->
      route.sourceWindow.mem prime := by
  intro member
  unfold zeckendorfSolenoidPrimeReadback at member
  exact selectedPrime_source_mem_from_list route member

theorem zeckendorfSolenoidReadbackPrime_normalized_mem
    (route : ZeckendorfSolenoidSelectorRoute) {n prime : Nat} :
    prime ∈ zeckendorfSolenoidPrimeReadback route n ->
      route.normalizedChannel.window.mem prime := by
  intro member
  have sourceMember :
      route.farEnd.primeWindow.sourceWindow.mem prime :=
    zeckendorfSolenoidReadbackPrime_source_mem route member
  unfold ZeckendorfSolenoidSelectorRoute.normalizedChannel
  rw [route.farEnd.primeWindow.window_preserved]
  exact sourceMember

theorem zeckendorfSolenoidReadbackPrime_den_pos
    (route : ZeckendorfSolenoidSelectorRoute) {n prime : Nat} :
    prime ∈ zeckendorfSolenoidPrimeReadback route n ->
      0 < route.normalizedChannel.amp_den prime := by
  intro member
  exact route.farEnd.primeWindow.den_pos_on_source_window prime
    (zeckendorfSolenoidReadbackPrime_source_mem route member)

theorem zeckendorfSolenoidReadbackPrime_is_prime
    (route : ZeckendorfSolenoidSelectorRoute) {n prime : Nat} :
    prime ∈ zeckendorfSolenoidPrimeReadback route n ->
      BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime prime := by
  intro member
  exact BEDC.Derived.RHRoute.FinitePrimeWindow.All.mem
    route.sourceWindow.all_prime
    (zeckendorfSolenoidReadbackPrime_source_mem route member)

theorem zeckendorfSolenoidPrime_deterministic
    (route : ZeckendorfSolenoidSelectorRoute) (index : Nat)
    (left right : Nat)
    (left_eq : left = zeckendorfSolenoidPrime route index)
    (right_eq : right = zeckendorfSolenoidPrime route index) :
    left = right := by
  rw [left_eq, right_eq]

theorem zeckendorfSolenoidPrimeReadback_deterministic
    (route : ZeckendorfSolenoidSelectorRoute) (n : Nat)
    (left right : List Nat)
    (left_eq : left = zeckendorfSolenoidPrimeReadback route n)
    (right_eq : right = zeckendorfSolenoidPrimeReadback route n) :
    left = right := by
  rw [left_eq, right_eq]

theorem zeckendorfSolenoidCoordinateReadback_deterministic
    (route : ZeckendorfSolenoidSelectorRoute) (n : Nat)
    (left right : List Rat)
    (left_eq : left = zeckendorfSolenoidCoordinateReadback route n)
    (right_eq : right = zeckendorfSolenoidCoordinateReadback route n) :
    left = right := by
  rw [left_eq, right_eq]

end BEDC.Derived.RHRoute.ZeckendorfSolenoidSelector
