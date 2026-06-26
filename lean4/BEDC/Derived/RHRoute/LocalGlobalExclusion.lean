import BEDC.Derived.RHRoute.ChannelNormalForm

namespace BEDC.Derived.RHRoute.LocalGlobalExclusion

open BEDC.Derived.RHRoute.ChannelNormalForm
open BEDC.Derived.RHRoute.FinitePrimeWindow

universe u v

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev LocalTest := BEDC.Derived.RHRoute.FinitePrimeWindow.LocalTest
abbrev ChannelNormalForm := BEDC.Derived.RHRoute.ChannelNormalForm.ChannelNormalForm

structure LocalExclusionCert {α : Type u} (F : Fingerprint α) (x y : α) where
  window : PrimeWindow
  window_matches : window.elems = F.window.elems
  separated : SeparatedByWindow F x y

def LocalExclusionPredicate {α : Type u} (F : Fingerprint α) (x y : α)
    (W : PrimeWindow) : Prop :=
  W.elems = F.window.elems ∧ SeparatedByWindow F x y

def LocalExclusionTest {α : Type u} (F : Fingerprint α) (x y : α) :
    LocalTest (LocalExclusionCert F x y) where
  run := fun W cert =>
    if W.elems = cert.window.elems then true else false
  predicate := fun W cert => LocalExclusionPredicate F x y W
  sound := by
    intro W cert pass
    unfold LocalExclusionPredicate
    change (if W.elems = cert.window.elems then true else false) = true at pass
    by_cases h : W.elems = cert.window.elems
    · exact And.intro (h.trans cert.window_matches) cert.separated
    · rw [if_neg h] at pass
      cases pass

structure WindowCoverCompatible {α : Type u} (F : Fingerprint α) (x y : α)
    (left right : LocalExclusionCert F x y) where
  compatible :
    WindowCompatible (LocalExclusionTest F x y) left.window right.window left
  right_window_matches_source : right.window.elems = left.window.elems

structure GluedGlobalExclusion {α : Type u} {NF : Type v}
    (C : ChannelNormalForm α NF) (x y : α)
    (left right : LocalExclusionCert C.fingerprint x y) where
  glued_window :
    GluedWindowCertificate (LocalExclusionTest C.fingerprint x y)
      left.window right.window left
  left_embeds :
    (p : Nat) -> left.window.mem p -> glued_window.union_window.mem p
  right_embeds :
    (p : Nat) -> right.window.mem p -> glued_window.union_window.mem p
  separated : SeparatedByWindow C.fingerprint x y
  normal_forms_apart : C.normalize x ≠ C.normalize y

theorem local_exclusion_cert_separated {α : Type u} {F : Fingerprint α}
    {x y : α} :
    LocalExclusionCert F x y -> SeparatedByWindow F x y := by
  intro cert
  exact cert.separated

theorem local_exclusion_run_self {α : Type u} {F : Fingerprint α}
    {x y : α} (cert : LocalExclusionCert F x y) :
    (LocalExclusionTest F x y).run cert.window cert = true := by
  change (if cert.window.elems = cert.window.elems then true else false) = true
  rw [if_pos rfl]

theorem local_exclusion_window_sound {α : Type u} {F : Fingerprint α}
    {x y : α} (cert : LocalExclusionCert F x y) :
    LocalExclusionPredicate F x y cert.window := by
  exact (LocalExclusionTest F x y).sound cert.window cert
    (local_exclusion_run_self cert)

theorem local_window_compatible_from_matching {α : Type u} {F : Fingerprint α}
    {x y : α} (left right : LocalExclusionCert F x y)
    (same_window : right.window.elems = left.window.elems) :
    WindowCompatible (LocalExclusionTest F x y) left.window right.window left := by
  refine {
    left_pass := local_exclusion_run_self left
    right_pass := ?_
    agree_on_overlap := ?_
  }
  · unfold LocalExclusionTest
    change (if right.window.elems = left.window.elems then true else false) = true
    rw [if_pos same_window]
  · intro p leftMember rightMember
    have leftPass : (LocalExclusionTest F x y).run left.window left = true :=
      local_exclusion_run_self left
    have rightPass : (LocalExclusionTest F x y).run right.window left = true := by
      change (if right.window.elems = left.window.elems then true else false) = true
      rw [if_pos same_window]
    exact leftPass.trans rightPass.symm

theorem local_cover_compatible_from_matching {α : Type u} {F : Fingerprint α}
    {x y : α} (left right : LocalExclusionCert F x y)
    (same_window : right.window.elems = left.window.elems) :
    WindowCoverCompatible F x y left right := by
  exact {
    compatible := local_window_compatible_from_matching left right same_window
    right_window_matches_source := same_window
  }

theorem GlobalExclusionFromLocal {α : Type u} {NF : Type v}
    (C : ChannelNormalForm α NF) {x y : α}
    (left right : LocalExclusionCert C.fingerprint x y)
    (cover : WindowCoverCompatible C.fingerprint x y left right) :
    ∃ glued : GluedGlobalExclusion C x y left right,
      glued.separated = left.separated ∧
        glued.normal_forms_apart = finite_prime_fingerprint_separation C left.separated := by
  have gluedExists :=
    finite_prime_window_gluing (LocalExclusionTest C.fingerprint x y)
      left.window right.window left cover.compatible
  cases gluedExists with
  | intro cert certRows =>
      exact ⟨{
        glued_window := cert
        left_embeds := certRows.right.left
        right_embeds := certRows.right.right
        separated := left.separated
        normal_forms_apart := finite_prime_fingerprint_separation C left.separated
      }, And.intro rfl rfl⟩

theorem GlobalExclusionFromLocal_absurd {α : Type u} {NF : Type v}
    (C : ChannelNormalForm α NF) {x y : α}
    (left right : LocalExclusionCert C.fingerprint x y)
    (cover : WindowCoverCompatible C.fingerprint x y left right) :
    C.normalize x = C.normalize y -> False := by
  intro normalEqual
  have global := GlobalExclusionFromLocal C left right cover
  cases global with
  | intro glued _rows =>
      exact glued.normal_forms_apart normalEqual

theorem GlobalExclusionFromAllLocal {α : Type u} {NF : Type v}
    (C : ChannelNormalForm α NF) {x y : α}
    (windows : List (LocalExclusionCert C.fingerprint x y))
    (source : LocalExclusionCert C.fingerprint x y)
    (all_local :
      All (fun cert : LocalExclusionCert C.fingerprint x y =>
        WindowCoverCompatible C.fingerprint x y source cert) windows)
    (selected : LocalExclusionCert C.fingerprint x y)
    (member : selected ∈ windows) :
    ∃ glued : GluedGlobalExclusion C x y source selected,
      glued.separated = source.separated ∧
        glued.normal_forms_apart = finite_prime_fingerprint_separation C source.separated := by
  have selectedCover :
      WindowCoverCompatible C.fingerprint x y source selected :=
    All.mem all_local member
  exact GlobalExclusionFromLocal C source selected selectedCover

theorem GlobalExclusionFromAllLocal_absurd {α : Type u} {NF : Type v}
    (C : ChannelNormalForm α NF) {x y : α}
    (windows : List (LocalExclusionCert C.fingerprint x y))
    (source : LocalExclusionCert C.fingerprint x y)
    (all_local :
      All (fun cert : LocalExclusionCert C.fingerprint x y =>
        WindowCoverCompatible C.fingerprint x y source cert) windows)
    (selected : LocalExclusionCert C.fingerprint x y)
    (member : selected ∈ windows) :
    C.normalize x = C.normalize y -> False := by
  intro normalEqual
  have global := GlobalExclusionFromAllLocal C windows source all_local selected member
  cases global with
  | intro glued _rows =>
      exact glued.normal_forms_apart normalEqual

end BEDC.Derived.RHRoute.LocalGlobalExclusion
