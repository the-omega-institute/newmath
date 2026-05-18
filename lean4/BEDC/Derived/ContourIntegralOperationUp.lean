import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContourIntegralOperationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
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

theorem ContourIntegralOperationNameCertObligations [AskSetup] [PackageSetup]
    {G F S M I H P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContourIntegralOperationCarrier G F S M I H P N ->
      PkgSig bundle P pkg ->
        SemanticNameCert
          (fun row : BHist => ContourIntegralOperationCarrier G F S M I H P N ∧ hsame row N)
          (fun row : BHist =>
            hsame row G ∨ hsame row F ∨ hsame row S ∨ hsame row M ∨ hsame row I ∨
              hsame row N)
          (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N ∧ hsame H (append G F))
          hsame ∧
            UnaryHistory I ∧ UnaryHistory N ∧ hsame H (append G F) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert
  intro carrier pkgP
  have routeClosure := ContourIntegralOperationCarrier_riemann_sum_route_closure carrier
  have unaryI : UnaryHistory I := routeClosure.left
  have unaryN : UnaryHistory N := routeClosure.right.left
  have sameInputFace : hsame H (append G F) := routeClosure.right.right
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro N (And.intro carrier (hsame_refl N))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row other same
          exact hsame_symm same
        equiv_trans := by
          intro row middle other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))
      ledger_sound := by
        intro row source
        exact And.intro pkgP (And.intro source.right sameInputFace)
    }
  · exact And.intro unaryI (And.intro unaryN (And.intro sameInputFace pkgP))

end BEDC.Derived.ContourIntegralOperationUp
