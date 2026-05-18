import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

theorem ContourIntegralOperationCarrier_namecert_obligations {G F S M I H P N : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N ->
      SemanticNameCert
        (fun row : BHist => ContourIntegralOperationCarrier G F S M I H P N ∧ hsame row N)
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          UnaryHistory G ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory M ∧
            UnaryHistory I ∧ UnaryHistory N ∧ hsame row N ∧ hsame H (append G F) ∧
              Cont S M I ∧ Cont I P N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have sourceCarrier := carrier
  obtain ⟨unaryG, unaryF, unaryS, unaryM, unaryP, sameInputFace, integralRoute,
    exportRoute⟩ := carrier
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryI unaryP exportRoute
  constructor
  · constructor
    · exact Exists.intro N ⟨sourceCarrier, hsame_refl N⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row source
    exact ⟨source.right, unary_transport unaryN (hsame_symm source.right)⟩
  · intro _row source
    exact
      ⟨unaryG, unaryF, unaryS, unaryM, unaryI, unaryN, source.right, sameInputFace,
        integralRoute, exportRoute⟩

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

theorem ContourIntegralOperationCarrier_residue_consumer_boundary
    {G F S M I H P N residueRead hostTail : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N ->
      Cont I P residueRead ->
        UnaryHistory I ∧ UnaryHistory residueRead ∧ hsame H (append G F) ∧ Cont S M I ∧
          Cont I P residueRead ∧ (Cont residueRead (BHist.e0 hostTail) I -> False) ∧
            (Cont residueRead (BHist.e1 hostTail) I -> False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier residueRoute
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
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryResidueRead : UnaryHistory residueRead :=
    unary_cont_closed unaryI unaryP residueRoute
  have e0Refusal : Cont residueRead (BHist.e0 hostTail) I -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.left residueRoute back
  have e1Refusal : Cont residueRead (BHist.e1 hostTail) I -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.right residueRoute back
  exact
    ⟨unaryI, unaryResidueRead, sameInputFace, integralRoute, residueRoute, e0Refusal,
      e1Refusal⟩

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

theorem ContourIntegralOperationClassifierStability
    {G F S M I H P N G' F' S' M' I' H' P' N' : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N ->
      hsame G G' ->
        hsame F F' ->
          hsame S S' ->
            hsame M M' ->
              hsame P P' ->
                hsame H' (append G' F') ->
                  Cont S' M' I' ->
                    Cont I' P' N' ->
                      ContourIntegralOperationCarrier G' F' S' M' I' H' P' N' ∧
                        UnaryHistory I' ∧ UnaryHistory N' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier sameG sameF sameS sameM sameP sameInputFace' integralRoute' exportRoute'
  obtain
    ⟨unaryG, unaryF, unaryS, unaryM, unaryP, _sameInputFace, _integralRoute,
      _exportRoute⟩ :=
      carrier
  have unaryG' : UnaryHistory G' :=
    unary_transport unaryG sameG
  have unaryF' : UnaryHistory F' :=
    unary_transport unaryF sameF
  have unaryS' : UnaryHistory S' :=
    unary_transport unaryS sameS
  have unaryM' : UnaryHistory M' :=
    unary_transport unaryM sameM
  have unaryP' : UnaryHistory P' :=
    unary_transport unaryP sameP
  have unaryI' : UnaryHistory I' :=
    unary_cont_closed unaryS' unaryM' integralRoute'
  have unaryN' : UnaryHistory N' :=
    unary_cont_closed unaryI' unaryP' exportRoute'
  exact
    ⟨⟨unaryG', unaryF', unaryS', unaryM', unaryP', sameInputFace', integralRoute',
        exportRoute'⟩,
      unaryI', unaryN'⟩

end BEDC.Derived.ContourIntegralOperationUp
