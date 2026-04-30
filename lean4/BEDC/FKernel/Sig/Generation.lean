import BEDC.FKernel.Sig
import BEDC.FKernel.Sig.Determinacy
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Step

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sigRel_generation_cases [AskSetup] {bundle : ProbeBundle ProbeName} {h r : BHist} :
    SigRel bundle h r →
      (bundle = (ProbeBundle.Bnil : ProbeBundle ProbeName) ∧ hsame r BHist.Empty) ∨
        ∃ pi : ProbeName, ∃ tail : ProbeBundle ProbeName, ∃ s : BHist, ∃ m : BMark,
          ∃ delta : Evidence,
            bundle = ProbeBundle.Bcons pi tail ∧ Ask pi h m delta ∧ SigRel tail h s ∧
              Ext s m r := by
  intro hsig
  cases hsig with
  | empty h =>
      exact Or.inl (And.intro rfl rfl)
  | cons pi tail h s r m delta hask htail hext =>
      exact
        Or.inr
          (Exists.intro pi
            (Exists.intro tail
              (Exists.intro s
                (Exists.intro m
                  (Exists.intro delta
                    (And.intro rfl
                      (And.intro hask
                        (And.intro htail hext))))))))

theorem sigRel_generation_constructor_pair [AskSetup] :
    (forall h : BHist, SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h BHist.Empty) /\
    (forall {pi : ProbeName} {tail : ProbeBundle ProbeName} {h s r : BHist} {m : BMark}
      {delta : Evidence}, Ask pi h m delta -> SigRel tail h s -> Ext s m r ->
        SigRel (ProbeBundle.Bcons pi tail) h r) /\
    (forall {bundle : ProbeBundle ProbeName} {h r : BHist}, SigRel bundle h r ->
      (bundle = ProbeBundle.Bnil /\ hsame r BHist.Empty) \/
        exists pi : ProbeName, exists tail : ProbeBundle ProbeName, exists s : BHist,
        exists m : BMark, exists delta : Evidence,
          bundle = ProbeBundle.Bcons pi tail /\ Ask pi h m delta /\ SigRel tail h s /\
            Ext s m r) := by
  constructor
  · intro h
    exact SigRel.empty h
  · constructor
    · intro pi tail h s r m delta hask htail hext
      exact SigRel.cons pi tail h s r m delta hask htail hext
    · intro bundle h r hsig
      cases hsig with
      | empty h =>
          exact Or.inl (And.intro rfl rfl)
      | cons pi tail h s r m delta hask htail hext =>
          exact
            Or.inr
              (Exists.intro pi
                (Exists.intro tail
                  (Exists.intro s
                    (Exists.intro m
                      (Exists.intro delta
                        (And.intro rfl
                          (And.intro hask
                            (And.intro htail hext))))))))

theorem signature_event_generation_pack [AskSetup] :
    (forall h : BHist, SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h BHist.Empty) /\
    (forall {pi : ProbeName} {tail : ProbeBundle ProbeName} {h s r : BHist} {m : BMark}
      {delta : Evidence}, Ask pi h m delta -> SigRel tail h s -> Ext s m r ->
        SigRel (ProbeBundle.Bcons pi tail) h r) /\
    (forall {pi : ProbeName} {tail : ProbeBundle ProbeName} {h r : BHist},
      SigRel (ProbeBundle.Bcons pi tail) h r ->
        exists s : BHist, exists m : BMark, exists delta : Evidence,
          Ask pi h m delta /\ SigRel tail h s /\ Ext s m r) := by
  constructor
  · intro h
    exact SigRel.empty h
  · constructor
    · intro pi tail h s r m delta hask htail hext
      exact SigRel.cons pi tail h s r m delta hask htail hext
    · intro pi tail h r hsig
      cases hsig with
      | cons _ _ _ s _ m delta hask htail hext =>
          exact Exists.intro s
            (Exists.intro m
              (Exists.intro delta
                (And.intro hask
                  (And.intro htail hext))))

theorem sigRel_bundleAppend [AskSetup] {left right : ProbeBundle ProbeName}
    {h s t : BHist} :
    SigRel left h s -> SigRel right h t ->
      exists u : BHist,
        BEDC.FKernel.Cont.Cont t s u /\ SigRel (bundleAppend left right) h u := by
  intro hleft hright
  induction hleft with
  | empty h =>
      exact Exists.intro t (And.intro (cont_right_unit t) hright)
  | cons pi tail h s r m delta hask htail hext ih =>
      cases ih hright with
      | intro u data =>
          cases data with
          | intro hcont hsig =>
              cases hext with
              | e0 =>
                  exact Exists.intro (BHist.e0 u)
                    (And.intro (cont_step_zero hcont)
                      (SigRel.cons pi (bundleAppend tail right) h u (BHist.e0 u)
                        BMark.b0 delta hask hsig (Ext.e0 u)))
              | e1 =>
                  exact Exists.intro (BHist.e1 u)
                    (And.intro (cont_step_one hcont)
                      (SigRel.cons pi (bundleAppend tail right) h u (BHist.e1 u)
                        BMark.b1 delta hask hsig (Ext.e1 u)))

theorem sigRel_bundleAppend_inversion [AskSetup] {left right : ProbeBundle ProbeName}
    {h u : BHist} :
    SigRel (bundleAppend left right) h u ->
      exists s : BHist, exists t : BHist,
        SigRel left h s /\ SigRel right h t /\ Cont t s u := by
  intro hsig
  induction left generalizing u with
  | Bnil =>
      exact Exists.intro BHist.Empty
        (Exists.intro u
          (And.intro (SigRel.empty h)
            (And.intro hsig (cont_right_unit u))))
  | Bcons pi tail ih =>
      cases hsig with
      | cons _ _ _ tailAppendResult _ m delta hask tailAppendSig finalExt =>
          cases ih tailAppendSig with
          | intro tailLeftResult rest =>
              cases rest with
              | intro rightResult data =>
                  cases data with
                  | intro tailLeftSig tailData =>
                      cases tailData with
                      | intro rightSig tailCont =>
                          cases finalExt with
                          | e0 =>
                              exact Exists.intro (BHist.e0 tailLeftResult)
                                (Exists.intro rightResult
                                  (And.intro
                                    (SigRel.cons pi tail h tailLeftResult
                                      (BHist.e0 tailLeftResult) BMark.b0 delta hask
                                      tailLeftSig (Ext.e0 tailLeftResult))
                                    (And.intro rightSig (cont_step_zero tailCont))))
                          | e1 =>
                              exact Exists.intro (BHist.e1 tailLeftResult)
                                (Exists.intro rightResult
                                  (And.intro
                                    (SigRel.cons pi tail h tailLeftResult
                                      (BHist.e1 tailLeftResult) BMark.b1 delta hask
                                      tailLeftSig (Ext.e1 tailLeftResult))
                                    (And.intro rightSig (cont_step_one tailCont))))

theorem sameSig_bundleAppend_closure [AskSetup] {left right : ProbeBundle ProbeName}
    {h k : BHist} :
    SameSig left h k -> SameSig right h k -> SameSig (bundleAppend left right) h k := by
  intro leftSame rightSame
  cases leftSame with
  | intro leftH leftRest =>
      cases leftRest with
      | intro leftK leftData =>
          cases leftData with
          | intro leftHSig leftTail =>
              cases leftTail with
              | intro leftKSig leftResultsSame =>
                  cases rightSame with
                  | intro rightH rightRest =>
                      cases rightRest with
                      | intro rightK rightData =>
                          cases rightData with
                          | intro rightHSig rightTail =>
                              cases rightTail with
                              | intro rightKSig rightResultsSame =>
                                  cases sigRel_bundleAppend leftHSig rightHSig with
                                  | intro appendH appendHData =>
                                      cases appendHData with
                                      | intro contH appendHSig =>
                                          cases sigRel_bundleAppend leftKSig rightKSig with
                                          | intro appendK appendKData =>
                                              cases appendKData with
                                              | intro contK appendKSig =>
                                                  exact Exists.intro appendH
                                                    (Exists.intro appendK
                                                      (And.intro appendHSig
                                                        (And.intro appendKSig
                                                          (cont_respects_hsame rightResultsSame
                                                            leftResultsSame contH contK))))

theorem signature_generation_bundle_append [AskSetup] {left right : ProbeBundle ProbeName}
    {h s t : BHist} :
    SigRel left h s → SigRel right h t →
      ∃ u : BHist, Cont t s u ∧ SigRel (bundleAppend left right) h u := by
  intro leftSig rightSig
  induction leftSig with
  | empty h =>
      exact Exists.intro t (And.intro rfl rightSig)
  | cons pi tail h tailResult result m delta hask tailSig step ih =>
      cases ih rightSig with
      | intro joined joinedData =>
          cases joinedData with
          | intro hcont joinedSig =>
              cases step
              ·
                  exact Exists.intro (BHist.e0 joined)
                    (And.intro
                      (cont_ext_right_step hcont (Ext.e0 tailResult) (Ext.e0 joined))
                      (SigRel.cons pi (bundleAppend tail right) h joined (BHist.e0 joined)
                        BMark.b0 delta hask joinedSig (Ext.e0 joined)))
              ·
                  exact Exists.intro (BHist.e1 joined)
                     (And.intro
                       (cont_ext_right_step hcont (Ext.e1 tailResult) (Ext.e1 joined))
                       (SigRel.cons pi (bundleAppend tail right) h joined (BHist.e1 joined)
                         BMark.b1 delta hask joinedSig (Ext.e1 joined)))

theorem signature_generation_bundle_append_inversion [AskSetup]
    {left right : ProbeBundle ProbeName} {h u : BHist} :
    SigRel (bundleAppend left right) h u ->
      exists s : BHist, exists t : BHist,
        SigRel left h s /\ SigRel right h t /\ Cont t s u := by
  intro appended
  induction left generalizing u with
  | Bnil =>
      exact Exists.intro BHist.Empty
        (Exists.intro u
          (And.intro (SigRel.empty h)
            (And.intro appended (cont_right_unit u))))
  | Bcons pi tail ih =>
      cases appended with
      | cons _ _ _ joined _ m delta hask tailAppendSig step =>
          cases ih tailAppendSig with
          | intro tailResult recovered =>
              cases recovered with
              | intro rightResult recoveredData =>
                  cases recoveredData with
                  | intro tailSig rightData =>
                      cases rightData with
                      | intro rightSig tailCont =>
                          cases step with
                          | e0 =>
                              exact Exists.intro (BHist.e0 tailResult)
                                (Exists.intro rightResult
                                  (And.intro
                                    (SigRel.cons pi tail h tailResult
                                      (BHist.e0 tailResult) BMark.b0 delta hask tailSig
                                      (Ext.e0 tailResult))
                                    (And.intro rightSig (cont_step_zero tailCont))))
                          | e1 =>
                              exact Exists.intro (BHist.e1 tailResult)
                                (Exists.intro rightResult
                                  (And.intro
                                    (SigRel.cons pi tail h tailResult
                                      (BHist.e1 tailResult) BMark.b1 delta hask tailSig
                                      (Ext.e1 tailResult))
                                    (And.intro rightSig (cont_step_one tailCont))))

theorem signature_generation_three_bundle_coherence [AskSetup]
    {left middle right : ProbeBundle ProbeName} {h s t w : BHist} :
    SigRel left h s -> SigRel middle h t -> SigRel right h w ->
      exists a : BHist, exists b : BHist, exists uL : BHist, exists uR : BHist,
        SigRel (bundleAppend left middle) h a /\ Cont t s a /\
        SigRel (bundleAppend (bundleAppend left middle) right) h uL /\ Cont w a uL /\
        SigRel (bundleAppend middle right) h b /\ Cont w t b /\
        SigRel (bundleAppend left (bundleAppend middle right)) h uR /\ Cont b s uR /\
        hsame uL uR := by
  intro leftSig middleSig rightSig
  cases signature_generation_bundle_append leftSig middleSig with
  | intro a leftMiddle =>
      cases leftMiddle with
      | intro middleOverLeft leftMiddleSig =>
          cases signature_generation_bundle_append leftMiddleSig rightSig with
          | intro uL leftGrouped =>
              cases leftGrouped with
              | intro rightOverLeftMiddle leftGroupedSig =>
                  cases signature_generation_bundle_append middleSig rightSig with
                  | intro b middleRight =>
                      cases middleRight with
                      | intro rightOverMiddle middleRightSig =>
                          cases signature_generation_bundle_append leftSig middleRightSig with
                          | intro uR rightGrouped =>
                              cases rightGrouped with
                              | intro middleRightOverLeft rightGroupedSig =>
                                  exact
                                    ⟨a, b, uL, uR, leftMiddleSig, middleOverLeft,
                                      leftGroupedSig, rightOverLeftMiddle, middleRightSig,
                                      rightOverMiddle, rightGroupedSig, middleRightOverLeft,
                                      hsame_symm
                                        (cont_assoc_hsame rightOverMiddle middleRightOverLeft
                                          middleOverLeft rightOverLeftMiddle)⟩

theorem signature_generation_append_component_determinacy [AskSetup]
    {left right : ProbeBundle ProbeName} {D : BHist -> Prop} {h s t u : BHist} :
    BundleAskPolicy left D -> BundleAskPolicy right D -> D h -> SigRel left h s ->
      SigRel right h t -> SigRel (bundleAppend left right) h u ->
        exists v : BHist, Cont t s v /\ hsame v u := by
  intro leftPolicy rightPolicy hdom leftSig rightSig appendedSig
  have appendPolicy : BundleAskPolicy (bundleAppend left right) D :=
    bundleAskPolicy_append_gluing leftPolicy rightPolicy
  cases signature_generation_bundle_append leftSig rightSig with
  | intro v appendData =>
      cases appendData with
      | intro hcont generatedSig =>
          have sameResult : hsame v u :=
            sig_deterministic_from_bundle_policy appendPolicy hdom generatedSig appendedSig
          exact Exists.intro v (And.intro hcont sameResult)

end BEDC.FKernel.Sig
