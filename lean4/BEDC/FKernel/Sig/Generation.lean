import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
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

end BEDC.FKernel.Sig
