import BEDC.Derived.IntUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.Derived.IntUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def RingOfIntegersDedekindSourceCarrier [AskSetup] [PackageSetup]
    (num embedded embedding equation classifier contRow provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  IntCarrier BEDC.FKernel.Mark.BMark.b0 embedded ∧ Cont embedded num embedding ∧
    Cont embedding equation contRow ∧ hsame classifier contRow ∧
      Cont provenance contRow endpoint ∧ PkgSig bundle endpoint pkg

theorem RingOfIntegersDedekindSourceCarrier_classifier_transport [AskSetup] [PackageSetup]
    {num embedded embedding equation classifier contRow provenance endpoint embedded'
      embedding' contRow' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersDedekindSourceCarrier num embedded embedding equation classifier contRow
        provenance endpoint bundle pkg ->
      hsame embedded embedded' ->
        Cont embedded' num embedding' ->
          Cont embedding' equation contRow' ->
            Cont provenance contRow' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                RingOfIntegersDedekindSourceCarrier num embedded' embedding' equation
                    classifier contRow' provenance endpoint' bundle pkg ∧
                  hsame embedding embedding' ∧ hsame contRow contRow' := by
  intro carrier sameEmbedded embeddingCont' contRowCont' endpointCont' pkgSig'
  have embeddedCarrier' :
      IntCarrier BEDC.FKernel.Mark.BMark.b0 embedded' :=
    IntCarrier_magnitude_hsame_transport carrier.left sameEmbedded
  have sameEmbedding : hsame embedding embedding' :=
    cont_respects_hsame sameEmbedded (hsame_refl num) carrier.right.left embeddingCont'
  have sameContRow : hsame contRow contRow' :=
    cont_respects_hsame sameEmbedding (hsame_refl equation) carrier.right.right.left
      contRowCont'
  have sameClassifierContRow' : hsame classifier contRow' :=
    hsame_trans carrier.right.right.right.left sameContRow
  have carrier' :
      RingOfIntegersDedekindSourceCarrier num embedded' embedding' equation classifier
        contRow' provenance endpoint' bundle pkg :=
    And.intro embeddedCarrier'
      (And.intro embeddingCont'
        (And.intro contRowCont'
          (And.intro sameClassifierContRow'
            (And.intro endpointCont' pkgSig'))))
  exact And.intro carrier' (And.intro sameEmbedding sameContRow)

end BEDC.Derived.RingOfIntegersUp
