import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContourIntegralOperationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ContourIntegralOperationCarrier (G F S M I H P N : BHist) : Prop :=
  UnaryHistory G ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory M ∧
    UnaryHistory P ∧ hsame H (append G F) ∧ Cont S M I ∧ Cont I P N

theorem ContourIntegralOperationCarrier_riemann_sum_route_closure {G F S M I H P N : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N →
      UnaryHistory I ∧ UnaryHistory N ∧ hsame H (append G F) := by
  intro packet
  have unaryS : UnaryHistory S :=
    packet.right.right.left
  have unaryM : UnaryHistory M :=
    packet.right.right.right.left
  have unaryP : UnaryHistory P :=
    packet.right.right.right.right.left
  have sameInputFace : hsame H (append G F) :=
    packet.right.right.right.right.right.left
  have integralRoute : Cont S M I :=
    packet.right.right.right.right.right.right.left
  have exportRoute : Cont I P N :=
    packet.right.right.right.right.right.right.right
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryI unaryP exportRoute
  exact ⟨unaryI, unaryN, sameInputFace⟩

theorem ContourIntegralOperationCarrier_pl_contour_boundary {G F S M I H P N pathRead : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N →
      Cont G F pathRead →
        UnaryHistory pathRead ∧ hsame H (append G F) ∧
          UnaryHistory I ∧ UnaryHistory N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier pathRoute
  have unaryG : UnaryHistory G :=
    carrier.left
  have unaryF : UnaryHistory F :=
    carrier.right.left
  have unaryS : UnaryHistory S :=
    carrier.right.right.left
  have unaryM : UnaryHistory M :=
    carrier.right.right.right.left
  have unaryP : UnaryHistory P :=
    carrier.right.right.right.right.left
  have sameInputFace : hsame H (append G F) :=
    carrier.right.right.right.right.right.left
  have integralRoute : Cont S M I :=
    carrier.right.right.right.right.right.right.left
  have exportRoute : Cont I P N :=
    carrier.right.right.right.right.right.right.right
  have unaryPathRead : UnaryHistory pathRead :=
    unary_cont_closed unaryG unaryF pathRoute
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryI unaryP exportRoute
  exact ⟨unaryPathRead, sameInputFace, unaryI, unaryN⟩

theorem ContourIntegralOperationCarrier_operation_law_ledger_closure
    {G F S M I H P N lawRead publicRead : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N →
      Cont S M lawRead →
        Cont lawRead P publicRead →
          UnaryHistory lawRead ∧ UnaryHistory publicRead ∧ hsame H (append G F) ∧
            Cont S M lawRead ∧ Cont lawRead P publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier lawRoute publicRoute
  have unaryS : UnaryHistory S :=
    carrier.right.right.left
  have unaryM : UnaryHistory M :=
    carrier.right.right.right.left
  have unaryP : UnaryHistory P :=
    carrier.right.right.right.right.left
  have sameInputFace : hsame H (append G F) :=
    carrier.right.right.right.right.right.left
  have unaryLawRead : UnaryHistory lawRead :=
    unary_cont_closed unaryS unaryM lawRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryLawRead unaryP publicRoute
  exact ⟨unaryLawRead, unaryPublicRead, sameInputFace, lawRoute, publicRoute⟩

theorem ContourIntegralOperationModulusTransport {G F S M I H P N M' outputRead : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N ->
      hsame M M' ->
        Cont S M' outputRead ->
          UnaryHistory M' ∧ UnaryHistory outputRead ∧ hsame H (append G F) ∧
            Cont S M' outputRead ∧ UnaryHistory N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier sameModulus outputRoute
  have unaryS : UnaryHistory S :=
    carrier.right.right.left
  have unaryM : UnaryHistory M :=
    carrier.right.right.right.left
  have unaryP : UnaryHistory P :=
    carrier.right.right.right.right.left
  have sameInputFace : hsame H (append G F) :=
    carrier.right.right.right.right.right.left
  have integralRoute : Cont S M I :=
    carrier.right.right.right.right.right.right.left
  have exportRoute : Cont I P N :=
    carrier.right.right.right.right.right.right.right
  have unaryM' : UnaryHistory M' :=
    unary_transport unaryM sameModulus
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryS unaryM' outputRoute
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryI unaryP exportRoute
  exact ⟨unaryM', outputReadUnary, sameInputFace, outputRoute, unaryN⟩

theorem ContourIntegralOperationPublicExport {G F S M I H P N : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N ->
      UnaryHistory G ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory M ∧
        UnaryHistory I ∧ UnaryHistory N ∧ hsame H (append G F) ∧ Cont S M I ∧
          Cont I P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier
  obtain ⟨unaryG, unaryF, unaryS, unaryM, unaryP, sameInputFace, integralRoute,
    exportRoute⟩ := carrier
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryI unaryP exportRoute
  exact
    ⟨unaryG, unaryF, unaryS, unaryM, unaryI, unaryN, sameInputFace, integralRoute,
      exportRoute⟩

end BEDC.Derived.ContourIntegralOperationUp
