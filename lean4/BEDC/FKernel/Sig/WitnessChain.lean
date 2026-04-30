import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sameSig_trans_chain_witnesses_under_policy [AskSetup]
    {bundle : ProbeBundle ProbeName} {D : BHist -> Prop} (policy : AskPolicy D)
    {h k l s t u v : BHist} :
    D k -> SigRel bundle h s -> SigRel bundle k t -> hsame s t ->
      SigRel bundle k u -> SigRel bundle l v -> hsame u v ->
      exists _ : hsame t u, SameSig bundle h l := by
  intro hk hs ht hst hu hv huv
  have htu : hsame t u :=
    sig_deterministic
      (bundle := bundle)
      (D := D)
      (h := k)
      (s := t)
      (t := u)
      policy
      hk
      ht
      hu
  exact Exists.intro htu
    (Exists.intro s
      (Exists.intro v
        (And.intro hs
          (And.intro hv
            (hsame_trans hst (hsame_trans htu huv))))))

end BEDC.FKernel.Sig
