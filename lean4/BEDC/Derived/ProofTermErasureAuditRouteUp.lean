import BEDC.FKernel.Cont

namespace BEDC.Derived.ProofTermErasureAuditRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ProofTermErasureAuditRoute_erased_cont_replay
    {P E C R P' E' C' R' : BHist} (hP : hsame P P') (hC : hsame C C')
    (hR : hsame R R') (erasure : Cont P C E) (erasure' : Cont P' C' E') :
    hsame (append E R) (append E' R') := by
  cases hP
  cases hC
  cases hR
  cases erasure
  cases erasure'
  rfl

theorem ProofTermErasureAuditRoute_erased_replay_determinacy
    {P E T C R _S H Q N P' E' T' C' R' _S' H' Q' N' : BHist} (hP : hsame P P')
    (hT : hsame T T') (hC : hsame C C') (hR : hsame R R') (hH : hsame H H')
    (hQ : hsame Q Q') (hN : hsame N N') (erasure : Cont P C E)
    (erasure' : Cont P' C' E') :
    hsame
      (append E (append T (append C (append R (append H (append Q N))))))
      (append E' (append T' (append C' (append R' (append H' (append Q' N')))))) := by
  cases hP
  cases hT
  cases hC
  cases hR
  cases hH
  cases hQ
  cases hN
  cases erasure
  cases erasure'
  rfl

end BEDC.Derived.ProofTermErasureAuditRouteUp
