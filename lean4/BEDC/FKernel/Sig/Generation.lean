import BEDC.FKernel.Sig
import BEDC.FKernel.Cont

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

theorem sigRel_bundleAppend_forward [AskSetup] {left right : ProbeBundle ProbeName}
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

theorem sigRel_bundleAppend_generation [AskSetup] :
    forall {left right : ProbeBundle ProbeName} {h s t : BHist},
      SigRel left h s -> SigRel right h t ->
        exists u : BHist, Cont t s u /\ SigRel (bundleAppend left right) h u := by
  intro left right h s t leftSig rightSig
  induction leftSig generalizing right t with
  | empty h =>
      exact Exists.intro t (And.intro (cont_right_unit t) rightSig)
  | cons pi tail h s r m delta hask tailSig finalExt ih =>
      cases finalExt with
      | e0 =>
          cases ih rightSig with
          | intro u tailData =>
              cases tailData with
              | intro tailCont tailAppendSig =>
                  exact Exists.intro (BHist.e0 u)
                    (And.intro
                      (cont_step_zero tailCont)
                      (SigRel.cons pi (bundleAppend tail right) h u (BHist.e0 u) BMark.b0
                        delta hask tailAppendSig (Ext.e0 u)))
      | e1 =>
          cases ih rightSig with
          | intro u tailData =>
              cases tailData with
              | intro tailCont tailAppendSig =>
                  exact Exists.intro (BHist.e1 u)
                    (And.intro
                      (cont_step_one tailCont)
                      (SigRel.cons pi (bundleAppend tail right) h u (BHist.e1 u) BMark.b1
                        delta hask tailAppendSig (Ext.e1 u)))

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
                                  cases sigRel_bundleAppend_generation leftHSig rightHSig with
                                  | intro appendH appendHData =>
                                      cases appendHData with
                                      | intro contH appendHSig =>
                                          cases sigRel_bundleAppend_generation leftKSig rightKSig with
                                          | intro appendK appendKData =>
                                              cases appendKData with
                                              | intro contK appendKSig =>
                                                  exact Exists.intro appendH
                                                    (Exists.intro appendK
                                                      (And.intro appendHSig
                                                        (And.intro appendKSig
                                                          (cont_respects_hsame rightResultsSame
                                                            leftResultsSame contH contK))))

end BEDC.FKernel.Sig
